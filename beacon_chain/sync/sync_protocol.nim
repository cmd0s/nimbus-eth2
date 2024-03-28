# beacon_chain
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  chronicles, chronos, snappy, snappy/codec,
  ../spec/datatypes/[phase0, altair, bellatrix, capella, deneb],
  ../spec/[helpers, forks, network],
  ".."/[beacon_clock],
  ../networking/eth2_network,
  ../consensus_object_pools/blockchain_dag,
  ../rpc/rest_constants

logScope:
  topics = "sync_proto"

const
  blockResponseCost = allowedOpsPerSecondCost(64)
    ## Allow syncing ~64 blocks/sec (minus request costs)
  blobResponseCost = allowedOpsPerSecondCost(1000)
    ## Multiple can exist per block, they are much smaller than blocks

type
  BeaconSyncNetworkState* {.final.} = ref object of RootObj
    dag: ChainDAGRef
    cfg: RuntimeConfig
    genesisBlockRoot: Eth2Digest

  BlockRootSlot* = object
    blockRoot: Eth2Digest
    slot: Slot

  BlockRootsList* = List[Eth2Digest, Limit MAX_REQUEST_BLOCKS]
  BlobIdentifierList* = List[BlobIdentifier, Limit (MAX_REQUEST_BLOB_SIDECARS)]

proc readChunkPayload*(
    conn: Connection, peer: Peer, MsgType: type (ref ForkedSignedBeaconBlock)):
    Future[NetRes[MsgType]] {.async: (raises: [CancelledError]).} =
  var contextBytes: ForkDigest
  try:
    await conn.readExactly(addr contextBytes, sizeof contextBytes)
  except CancelledError as exc:
    raise exc
  except CatchableError:
    return neterr UnexpectedEOF

  if contextBytes == peer.network.forkDigests.phase0:
    let res = await readChunkPayload(conn, peer, phase0.SignedBeaconBlock)
    if res.isOk:
      return ok newClone(ForkedSignedBeaconBlock.init(res.get))
    else:
      return err(res.error)
  elif contextBytes == peer.network.forkDigests.altair:
    let res = await readChunkPayload(conn, peer, altair.SignedBeaconBlock)
    if res.isOk:
      return ok newClone(ForkedSignedBeaconBlock.init(res.get))
    else:
      return err(res.error)
  elif contextBytes == peer.network.forkDigests.bellatrix:
    let res = await readChunkPayload(conn, peer, bellatrix.SignedBeaconBlock)
    if res.isOk:
      return ok newClone(ForkedSignedBeaconBlock.init(res.get))
    else:
      return err(res.error)
  elif contextBytes == peer.network.forkDigests.capella:
    let res = await readChunkPayload(conn, peer, capella.SignedBeaconBlock)
    if res.isOk:
      return ok newClone(ForkedSignedBeaconBlock.init(res.get))
    else:
      return err(res.error)
  elif contextBytes == peer.network.forkDigests.deneb:
    let res = await readChunkPayload(conn, peer, deneb.SignedBeaconBlock)
    if res.isOk:
      return ok newClone(ForkedSignedBeaconBlock.init(res.get))
    else:
      return err(res.error)
  else:
    return neterr InvalidContextBytes

proc readChunkPayload*(
    conn: Connection, peer: Peer, MsgType: type (ref BlobSidecar)):
    Future[NetRes[MsgType]] {.async: (raises: [CancelledError]).} =
  var contextBytes: ForkDigest
  try:
    await conn.readExactly(addr contextBytes, sizeof contextBytes)
  except CancelledError as exc:
    raise exc
  except CatchableError:
    return neterr UnexpectedEOF

  if contextBytes == peer.network.forkDigests.deneb:
    let res = await readChunkPayload(conn, peer, BlobSidecar)
    if res.isOk:
      return ok newClone(res.get)
    else:
      return err(res.error)
  else:
    return neterr InvalidContextBytes

{.pop.} # TODO fix p2p macro for raises

p2pProtocol BeaconSync(version = 1,
                       networkState = BeaconSyncNetworkState):
  proc beaconBlocksByRange_v2(
      peer: Peer,
      startSlot: Slot,
      reqCount: uint64,
      reqStep: uint64,
      response: MultipleChunksResponse[
        ref ForkedSignedBeaconBlock, Limit MAX_REQUEST_BLOCKS])
      {.async, libp2pProtocol("beacon_blocks_by_range", 2).} =
    # TODO Semantically, this request should return a non-ref, but doing so
    #      runs into extreme inefficiency due to the compiler introducing
    #      hidden copies - in future nim versions with move support, this should
    #      be revisited
    # TODO This code is more complicated than it needs to be, since the type
    #      of the multiple chunks response is not actually used in this server
    #      implementation (it's used to derive the signature of the client
    #      function, not in the code below!)
    # TODO although you can't tell from this function definition, a magic
    #      client call that returns `seq[ref ForkedSignedBeaconBlock]` will
    #      will be generated by the libp2p macro - we guarantee that seq items
    #      are `not-nil` in the implementation
    # TODO reqStep is deprecated - future versions can remove support for
    #      values != 1: https://github.com/ethereum/consensus-specs/pull/2856

    trace "got range request", peer, startSlot,
                               count = reqCount, step = reqStep
    if reqCount == 0 or reqStep == 0:
      raise newException(InvalidInputsError, "Empty range requested")

    var blocks: array[MAX_REQUEST_BLOCKS.int, BlockId]
    let
      dag = peer.networkState.dag
      # Limit number of blocks in response
      count = int min(reqCount, blocks.lenu64)
      endIndex = count - 1
      startIndex =
        dag.getBlockRange(startSlot, reqStep,
                          blocks.toOpenArray(0, endIndex))

    var
      found = 0
      bytes: seq[byte]
