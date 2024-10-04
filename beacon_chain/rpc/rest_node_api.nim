# Copyright (c) 2021-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/algorithm,
  stew/byteutils,
  chronicles,
  eth/p2p/discoveryv5/enr,
  libp2p/[multiaddress, multicodec, peerstore],
  ../version, ../beacon_node, ../sync/sync_manager,
  ../networking/[eth2_network, peer_pool],
  ../spec/datatypes/base,
  ./rest_utils

export rest_utils

logScope: topics = "rest_node"

type
  ConnectionStateSet* = set[ConnectionState]
  PeerTypeSet* = set[PeerType]

  RestNodePeerCount* = object
    disconnected*: uint64
    connecting*: uint64
    connected*: uint64
    disconnecting*: uint64

RestJson.useDefaultSerializationFor(
  RestNodePeerCount,
)

proc validateState(states: seq[PeerStateKind]): Result[ConnectionStateSet,
                                                       cstring] =
  var res: set[ConnectionState]
  for item in states:
    case item
    of PeerStateKind.Disconnected:
      if ConnectionState.Disconnected in res:
        return err("Peer connection states must be unique")
      res.incl(ConnectionState.Disconnected)
    of PeerStateKind.Connecting:
      if ConnectionState.Connecting in res:
        return err("Peer connection states must be unique")
      res.incl(ConnectionState.Connecting)
    of PeerStateKind.Connected:
      if ConnectionState.Connected in res:
        return err("Peer connection states must be unique")
      res.incl(ConnectionState.Connected)
    of PeerStateKind.Disconnecting:
      if ConnectionState.Disconnecting in res:
        return err("Peer connection states must be unique")
      res.incl(ConnectionState.Disconnecting)
  if res == {}:
    res = {ConnectionState.Connecting, ConnectionState.Connected,
           ConnectionState.Disconnecting, ConnectionState.Disconnected}
  ok(res)

proc validateDirection(directions: seq[PeerDirectKind]): Result[PeerTypeSet,
                                                                cstring] =
  var res: set[PeerType]
  for item in directions:
    case item
    of PeerDirectKind.Inbound:
      if PeerType.Incoming in res:
        return err("Peer direction states must be unique")
      res.incl(PeerType.Incoming)
    of PeerDirectKind.Outbound:
      if PeerType.Outgoing in res:
        return err("Peer direction states must be unique")
      res.incl(PeerType.Outgoing)
  if res == {}:
    res = {PeerType.Incoming, PeerType.Outgoing}
  ok(res)

proc toString(state: ConnectionState): string =
  case state
  of ConnectionState.Disconnected:
    "disconnected"
  of ConnectionState.Connecting:
    "connecting"
  of ConnectionState.Connected:
    "connected"
  of ConnectionState.Disconnecting:
    "disconnecting"
  else:
    ""

proc toString(direction: PeerType): string =
  case direction:
  of PeerType.Incoming:
    "inbound"
  of PeerType.Outgoing:
    "outbound"

proc getProtocolArgument(ma: MultiAddress,
                         codec: MultiCodec): MaResult[seq[byte]] =
  var buffer: seq[byte]
  for item in ma:
    let
      ritem = ? item
      code = ? ritem.protoCode()
    if code == codec:
      let arg = ? ritem.protoAddress()
      return ok(arg)
  err("Multiaddress codec has not been found")

proc getLastSeenAddress(node: BeaconNode, id: PeerId): string =
  # Because `last_seen_p2p_address` is single address but libp2p reports lot of
  # addresses, we going to sort list of addresses before selecting one. Here
  # sort order list:
  # 1. Globally routable IPv6 address.
  # 2. Globally routable IPv4 address.
  # 3. Non IPv4/IPv6 multiaddress.
  # 4. Site-local IPv6 address.
  # 5. Site-local IPv4 address.
  # 6. Link-local IPv6 address.
  # 7. Link-local IPv4 address.
  # 8. Loopback IPv6 address.
  # 9. Loopback IPv4 address.
  # 10. All other IPv6 address types.
  # 11. All other IPv4 address types.
  proc compare(
      a, b: tuple[address: MultiAddress, position: int]
  ): int {.closure.} = cmp(a.position, b.position)
  let addresses = node.network.switch.peerStore[AddressBook][id]
  var temp: seq[tuple[address: MultiAddress, position: int]]
  for address in addresses:
    let res =
      block:
        let
          isUDP = UDP.matchPartial(address)
          isTCP = TCP.matchPartial(address)

        if isUDP or isTCP:
          # TODO (cheatfate): We match TCP here because `nim-libp2p` do not have
          # QUIC support yet. So we give TCP addresses priority.
          let boost = if isUDP: 100 else: 0
          if IP4.matchPartial(address):
            let address4 =
              address.getProtocolArgument(multiCodec("ip4")).valueOr:
                continue
            var ta4 = TransportAddress(family: AddressFamily.IPv4)
            ta4.address_v4[0 .. 3] = address4[0 .. 3]
            if ta4.isLoopback():
              (address, boost + 9)
            elif ta4.isLinkLocal():
              (address, boost + 7)
            elif ta4.isSiteLocal():
              (address, boost + 5)
            elif ta4.isGlobal():
              (address, boost + 2)
            else:
              (address, boost + 11)
          elif IP6.matchPartial(address):
            let address6 =
              address.getProtocolArgument(multiCodec("ip6")).valueOr:
                continue
            var ta6 = TransportAddress(family: AddressFamily.IPv6)
            ta6.address_v6[0 .. 15] = address6[0 .. 15]
            if ta6.isLoopback():
              (address, boost + 8)
            elif ta6.isLinkLocal():
              (address, boost + 6)
            elif ta6.isSiteLocal():
              (address, boost + 4)
            elif ta6.isGlobal():
              (address, boost + 1)
            else:
              (address, boost + 10)
          else:
            (address, boost + 3)
        else:
          (address, 3)
    temp.add(res)

  if len(temp) > 0:
    sort(temp, compare, SortOrder.Ascending)
    $temp[0].address
  else:
    ""

proc getDiscoveryAddresses(node: BeaconNode): seq[string] =
  let
    typedRec = TypedRecord.fromRecord(node.network.enrRecord())
    peerAddr = typedRec.toPeerAddr(udpProtocol).valueOr:
      return default(seq[string])
    maddress = MultiAddress.init(multiCodec("p2p"), peerAddr.peerId).valueOr:
      return default(seq[string])

  var addresses: seq[string]
  for item in peerAddr.addrs:
    let res = concat(item, maddress)
    if res.isOk():
      addresses.add($(res.get()))
  addresses

proc getP2PAddresses(node: BeaconNode): seq[string] =
  let
    pinfo = node.network.switch.peerInfo
    maddress = MultiAddress.init(multiCodec("p2p"), pinfo.peerId).valueOr:
      return default(seq[string])

  var addresses: seq[string]
  for item in node.network.announcedAddresses:
    let res = concat(item, maddress)
    if res.isOk():
      addresses.add($(res.get()))
  for item in pinfo.addrs:
    let res = concat(item, maddress)
    if res.isOk():
      addresses.add($(res.get()))
  addresses

proc installNodeApiHandlers*(router: var RestRouter, node: BeaconNode) =
  let
    cachedVersion =
      RestApiResponse.prepareJsonResponse((version: nimbusAgentStr))

  # https://ethereum.github.io/beacon-APIs/#/Node/getNetworkIdentity
  router.api2(MethodGet, "/eth/v1/node/identity") do () -> RestApiResponse:
    RestApiResponse.jsonResponse(
      (
        peer_id: $node.network.peerId(),
        enr: node.network.enrRecord().toURI(),
        p2p_addresses: node.getP2PAddresses(),
        discovery_addresses: node.getDiscoveryAddresses(),
        metadata: (
          seq_number: node.network.metadata.seq_number,
          syncnets: to0xHex(node.network.metadata.syncnets.bytes),
          attnets: to0xHex(node.network.metadata.attnets.bytes)
        )
      )
    )

  # https://ethereum.github.io/beacon-APIs/#/Node/getPeers
  router.api2(MethodGet, "/eth/v1/node/peers") do (
    state: seq[PeerStateKind],
    direction: seq[PeerDirectKind]) -> RestApiResponse:
    let connectionMask =
      block:
        if state.isErr():
          return RestApiResponse.jsonError(Http400, InvalidPeerStateValueError,
                                           $state.error())
        validateState(state.get()).valueOr:
          return RestApiResponse.jsonError(Http400, InvalidPeerStateValueError,
                                           $error)
    let directionMask =
      block:
        if direction.isErr():
          return RestApiResponse.jsonError(Http400,
                                           InvalidPeerDirectionValueError,
                                           $direction.error())
        validateDirection(direction.get()).valueOr:
          return RestApiResponse.jsonError(Http400,
                                           InvalidPeerDirectionValueError,
                                           $error)
    var res: seq[RestNodePeer]
    for peer in node.network.peers.values():
      if (peer.connectionState in connectionMask) and
         (peer.direction in directionMask):
        let peer = RestNodePeer(
          peer_id: $peer.peerId,
          enr: if peer.enr.isSome(): peer.enr.get().toURI() else: "",
          last_seen_p2p_address: getLastSeenAddress(node, peer.peerId),
          state: peer.connectionState.toString(),
          direction: peer.direction.toString(),
          # Fields `agent` and `proto` are not part of specification
          agent: node.network.switch.peerStore[AgentBook][peer.peerId],
          proto: node.network.switch.peerStore[ProtoVersionBook][peer.peerId]
        )
        res.add(peer)
    RestApiResponse.jsonResponseWMeta(res, (count: RestNumeric(len(res))))

  # https://ethereum.github.io/beacon-APIs/#/Node/getPeerCount
  router.api2(MethodGet, "/eth/v1/node/peer_count") do () -> RestApiResponse:
    var res: RestNodePeerCount
    for item in node.network.peers.values():
      case item.connectionState
      of ConnectionState.Connecting:
        inc(res.connecting)
      of ConnectionState.Connected:
        inc(res.connected)
      of ConnectionState.Disconnecting:
        inc(res.disconnecting)
      of ConnectionState.Disconnected:
        inc(res.disconnected)
      of ConnectionState.None:
        discard
    RestApiResponse.jsonResponse(res)

  # https://ethereum.github.io/beacon-APIs/#/Node/getPeer
  router.api2(MethodGet, "/eth/v1/node/peers/{peer_id}") do (
    peer_id: PeerId) -> RestApiResponse:
    let peer =
      block:
        if peer_id.isErr():
          return RestApiResponse.jsonError(Http400, InvalidPeerIdValueError,
                                           $peer_id.error())
        let res = node.network.peers.getOrDefault(peer_id.get())
        if isNil(res):
          return RestApiResponse.jsonError(Http404, PeerNotFoundError)
        res
    RestApiResponse.jsonResponse(
      (
        peer_id: $peer.peerId,
        enr: if peer.enr.isSome(): peer.enr.get().toURI() else: "",
        last_seen_p2p_address: getLastSeenAddress(node, peer.peerId),
        state: peer.connectionState.toString(),
        direction: peer.direction.toString(),
        agent: node.network.switch.peerStore[AgentBook][peer.peerId],
          # Fields `agent` and `proto` are not part of specification
        proto: node.network.switch.peerStore[ProtoVersionBook][peer.peerId]
          # Fields `agent` and `proto` are not part of specification
      )
    )

  # https://ethereum.github.io/beacon-APIs/#/Node/getNodeVersion
  router.api2(MethodGet, "/eth/v1/node/version") do () -> RestApiResponse:
    RestApiResponse.response(cachedVersion, Http200, "application/json")

  # https://ethereum.github.io/beacon-APIs/#/Node/getSyncingStatus
  router.api2(MethodGet, "/eth/v1/node/syncing") do () -> RestApiResponse:
    let
      wallSlot = node.beaconClock.now().slotOrZero()
      headSlot = node.dag.head.slot
      distance = wallSlot - headSlot
      isSyncing =
        if isNil(node.syncManager):
          false
        else:
          node.syncManager.inProgress
      isOptimistic =
        if node.currentSlot().epoch() >= node.dag.cfg.BELLATRIX_FORK_EPOCH:
          some(not node.dag.head.executionValid)
        else:
          none[bool]()
      elOffline =
        if node.currentSlot().epoch() >= node.dag.cfg.CAPELLA_FORK_EPOCH:
          some(not node.elManager.hasAnyWorkingConnection)
        else:
          none[bool]()  # Added with ethereum/beacon-APIs v2.4.0

      info = RestSyncInfo(
        head_slot: headSlot, sync_distance: distance,
        is_syncing: isSyncing, is_optimistic: isOptimistic,
        el_offline: elOffline
      )
    RestApiResponse.jsonResponse(info)

  # https://ethereum.github.io/beacon-APIs/#/Node/getHealth
  router.api2(MethodGet, "/eth/v1/node/health") do () -> RestApiResponse:
    # TODO: Add ability to detect node's issues and return 503 error according
    # to specification.
    let status =
      if node.syncManager.inProgress:
        Http206
      else:
        Http200
    RestApiResponse.response(status)
