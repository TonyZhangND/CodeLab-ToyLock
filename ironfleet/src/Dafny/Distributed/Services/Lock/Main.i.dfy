include "../../Common/Framework/Main.s.dfy"
include "LockDistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"
include "../../Impl/Lock/Host.i.dfy"
include "AbstractService.s.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
// include "../../Protocol/Lock/RefinementProof/RefinementProof.i.dfy"
include "Marshall.i.dfy"

module Main_i refines Main_s {
    import opened DS_s = Lock_DistributedSystem_i
    import opened Environment_s
    import opened Concrete_NodeIdentity_i
    import opened PacketParsing_i
    import opened UdpLock_i
    import opened Host_i
    import opened AS_s = AbstractServiceLock_s
    import opened DistributedSystem_i
    // import opened RefinementProof_i
    import opened MarshallProof_i

    lemma RefinementProof(
        config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
        /*
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
        */
    {
        var lb := ImplToProtocol(config, db);
        sb := ProtocolToSpec(config, lb);
    }


 
    /* Takes a sequence of impolementation states and returns a corresponding sequence of 
    protocol states
    */
    lemma ImplToProtocol(config:ConcreteConfiguration, db:seq<DS_State>) returns (lb:seq<LS_State>) 
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |lb|; //
        ensures  LS_Init(lb[0], config); //
        ensures  forall i :: 0 <= i < |lb| - 1 ==>  LS_Next(lb[i], lb[i+1]);
        // ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {
        // Construct LS_State.environment
        var sentPackets := set p | p in db[0].environment.sentPackets :: LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)));
        var hostInfo := convertHostInfo(db[0].environment.hostInfo);
        var nextStep : LEnvStep<EndPoint, LockMessage>;
        match db[0].environment.nextStep  {
            // Construct environment.nextStep
            case LEnvStepHostIos(actor, ios)    => 
            {
                var new_ios := convertLEnvStepHostIos(ios);
                nextStep := LEnvStepHostIos(actor, new_ios);
            }
            case LEnvStepDeliverPacket(p)       => 
            {
                var new_packet := LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)));
                nextStep := LEnvStepDeliverPacket(new_packet);
            }
            case LEnvStepAdvanceTime            => 
                nextStep := LEnvStepAdvanceTime();
            case LEnvStepStutter                => 
                nextStep := LEnvStepStutter();
        }
        var env := LEnvironment(db[0].environment.time,
                                sentPackets,
                                hostInfo,
                                nextStep);

        // Construct LS_State.servers
        var servers :=   map s | s in db[0].servers :: db[0].servers[s].node;


        lb := [LS_State(env, servers)];
        
         // Convince Dafny: for all ep in config, there exists a unique i such that config[i] == ep
        assert forall e :: e in config <==> e in db[0].servers;
        reveal_SeqIsUnique();
        assert SeqIsUnique(config);
    }


    /* Helper: Takes a seq<LIoOp<EndPoint, seq<byte>>> belonging to a ds state and returns
    a corresponding seq<LIoOp<EndPoint, LockMessage>> belonging to an ls state 
    */
    lemma convertLEnvStepHostIos(s1: seq<LIoOp<EndPoint, seq<byte>>>) returns (s2: seq<LIoOp<EndPoint, LockMessage>>)
        ensures |s1| == |s2|;
        ensures forall i :: 0 <= i < |s1| ==> (
            s1[i].LIoOpSend? ==> s2[i] == LIoOpSend(LPacket(s1[i].s.dst, s1[i].s.src, AbstractifyCMessage(DemarshallData(s1[i].s.msg))))
        );
        ensures forall i :: 0 <= i < |s1| ==> (
            s1[i].LIoOpReceive? ==> s2[i] == LIoOpReceive(LPacket(s1[i].r.dst, s1[i].r.src, AbstractifyCMessage(DemarshallData(s1[i].r.msg))))
        );
        ensures forall i :: 0 <= i < |s1| ==> (
            s1[i].LIoOpTimeoutReceive? ==> s2[i] == LIoOpTimeoutReceive()
        );
        ensures forall i :: 0 <= i < |s1| ==> (
            s1[i].LIoOpReadClock? ==> s2[i] == LIoOpReadClock(s1[i].t)
        );
  {
        s2 := [];
        var i := 0;
        while (i < |s1|)
            decreases |s1| - i;
            invariant 0 <= i <= |s1|;
            invariant i == |s2|;
            invariant forall k :: 0 <= k < i ==> (
                s1[k].LIoOpSend? ==> s2[k] == LIoOpSend(LPacket(s1[k].s.dst, s1[k].s.src, AbstractifyCMessage(DemarshallData(s1[k].s.msg))))
            );
            invariant forall k :: 0 <= k < i ==> (
                s1[k].LIoOpReceive? ==> s2[k] == LIoOpReceive(LPacket(s1[k].r.dst, s1[k].r.src, AbstractifyCMessage(DemarshallData(s1[k].r.msg))))
            );
            invariant forall k :: 0 <= k < i ==> (
                s1[k].LIoOpTimeoutReceive? ==> s2[k] == LIoOpTimeoutReceive()
            );
            invariant forall k :: 0 <= k < i ==> (
                s1[k].LIoOpReadClock? ==> s2[k] == LIoOpReadClock(s1[k].t)
            );
        {
            match s1[i] {
                case LIoOpSend(s)               =>
                {
                    s2 := s2 + [LIoOpSend(LPacket(s.dst, s.src, AbstractifyCMessage(DemarshallData(s.msg))))];
                }
                case LIoOpReceive(r)            =>
                {
                    s2 := s2 + [LIoOpReceive(LPacket(r.dst, r.src, AbstractifyCMessage(DemarshallData(r.msg))))];
                }
                case LIoOpTimeoutReceive()      =>
                {
                    s2 := s2 + [LIoOpTimeoutReceive()];
                }
                case LIoOpReadClock(t)          =>
                {
                    s2 := s2 + [LIoOpReadClock(t)];
                }
            }
            i := i + 1;
        }
    }



    /* Helper: Takes a seq<LPacket<EndPoint, seq<byte>>> belonging to a ds state and 
    returns a corresponding seq<LPacket<EndPoint, LockMessage>> belonging 
    to a ls state */
    lemma byteSeqToLockMessageSeq(byte_seq:seq<LPacket<EndPoint, seq<byte>>>) returns (lock_msg_seq:seq<LPacket<EndPoint, LockMessage>>)
        ensures |byte_seq| == |lock_msg_seq|;
        ensures forall i :: 0 <= i < |byte_seq| ==> byte_seq[i].dst == lock_msg_seq[i].dst;
        ensures forall i :: 0 <= i < |byte_seq| ==> byte_seq[i].src == lock_msg_seq[i].src;
        ensures forall i :: 0 <= i < |byte_seq| ==> AbstractifyCMessage(DemarshallData(byte_seq[i].msg)) == lock_msg_seq[i].msg;
    {
        lock_msg_seq := [];
        var i := 0;
        while (i < |byte_seq|) 
            decreases |byte_seq| - i;
            invariant 0 <= i <= |byte_seq|;
            invariant |lock_msg_seq| == i;
            invariant forall k :: 0 <= k < i ==> byte_seq[k].dst == lock_msg_seq[k].dst;
            invariant forall k :: 0 <= k < i ==> byte_seq[k].src == lock_msg_seq[k].src;
            invariant forall k :: 0 <= k < i ==> AbstractifyCMessage(DemarshallData(byte_seq[k].msg)) == lock_msg_seq[k].msg;
        {
            var next_packet := LPacket(byte_seq[i].dst, byte_seq[i].src, AbstractifyCMessage(DemarshallData(byte_seq[i].msg)));
            lock_msg_seq := lock_msg_seq + [next_packet];
            i := i+1;
        }
        assert i == |lock_msg_seq| == |byte_seq|;
    }

    /* Helper: Takes a hostInfo:map<EndPoint, LHostInfo<EndPoint, seq<byte>>> belonging 
    to a ds state and returns a corresponding hostInfo:map<EndPoint, LHostInfo<EndPoint, LockMessage>> 
    belonging to a ls state */
    lemma convertHostInfo(h1: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>) returns (h2: map<EndPoint, LHostInfo<EndPoint, LockMessage>>) 
        ensures |h1| == |h2|; 
        ensures forall ep :: ep in h1 ==> ep in h2;
        ensures forall ep :: ep in h1 ==> |h1[ep].queue| == |h2[ep].queue|; 
        ensures forall ep :: ep in h1 ==> (forall i :: 0 <= i < |h1[ep].queue| ==> h1[ep].queue[i].dst == h2[ep].queue[i].dst);
        ensures forall ep :: ep in h1 ==> (forall i :: 0 <= i < |h1[ep].queue| ==> h1[ep].queue[i].src == h2[ep].queue[i].src);
        ensures forall ep :: ep in h1 ==> (forall i :: 0 <= i < |h1[ep].queue| ==> AbstractifyCMessage(DemarshallData(h1[ep].queue[i].msg)) == h2[ep].queue[i].msg);
    {
        h2 := map[];
        var keys := h1.Keys;
        while keys != {}
            decreases keys
            invariant h2.Keys <= h1.Keys;
            invariant keys + h2.Keys == h1.Keys;
            invariant |keys| + |h2| == |h1|;
            invariant forall ep :: ep in h1 && !(ep in keys) ==> ep in h2;
            invariant forall ep :: ep in h2 ==> |h1[ep].queue| == |h2[ep].queue|;
            invariant forall ep :: ep in h2 ==> (forall i :: 0 <= i < |h2[ep].queue| ==> h1[ep].queue[i].dst == h2[ep].queue[i].dst); 
            invariant forall ep :: ep in h2 ==> (forall i :: 0 <= i < |h2[ep].queue| ==> h1[ep].queue[i].src == h2[ep].queue[i].src); 
            invariant forall ep :: ep in h2 ==> (forall i :: 0 <= i < |h2[ep].queue| ==> AbstractifyCMessage(DemarshallData(h1[ep].queue[i].msg)) == h2[ep].queue[i].msg); 
        {
            var k :| k in keys;
            var lock_msg_queue := byteSeqToLockMessageSeq(h1[k].queue);
            h2 := h2[k := LHostInfo(lock_msg_queue)];
            keys := keys - {k};
        }
    }


    lemma ProtocolToSpec(config:ConcreteConfiguration, lb:seq<LS_State>) returns (sb:seq<ServiceState>)
        // requires |lb| > 0;
        // requires LS_Init(lb[0], config);
        // requires forall i :: 0 <= i < |lb| - 1 ==>  LS_Next(lb[i], lb[i+1]);
        // ensures  |lb| == |sb|;
        // ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(lb[0].servers));
        // ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        // ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {

    }
}
