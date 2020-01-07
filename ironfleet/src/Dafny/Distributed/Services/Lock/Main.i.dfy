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


    /*************************************************************************************
    * Main: Prove that the implementation conforms to the spec
    *************************************************************************************/

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
        // var lb := ImplToProtocol(config, db);
        // sb := ProtocolToSpec(config, lb);
    }


    /*************************************************************************************
    * Prove that the implementation conforms to the protocol
    *************************************************************************************/

 
    /* Takes a sequence of impolementation states and returns a corresponding sequence of 
    protocol states
    */
    lemma ImplToProtocol(config:ConcreteConfiguration, db:seq<DS_State>) returns (lb:seq<LS_State>) 
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires |db| > 0;
        requires DS_Init(db[0], config);
        // requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        requires forall i :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |lb|; 
        ensures  LS_Init(lb[0], config); 
        ensures  forall i :: 0 <= i < |lb| - 1 ==>  LS_Next(lb[i], lb[i+1]);
        // ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {
        // FIRST CONSTRUCT THE INITIAL PROTOCOL STATE
        // Construct LS_State.environment for initial state
        var env := convertEnv(db[0].environment);

        // Construct LS_State.servers for initial state
        var servers :=   map s | s in db[0].servers :: db[0].servers[s].node;

        lb := [LS_State(env, servers)];
        convertEnvLemma(db[0].environment, lb[0].environment);
        assert lb[0].environment == convertEnv(db[0].environment);
        
        // Convince Dafny: for all ep in config, there exists a unique i such that config[i] == ep
        assert forall e :: e in config <==> e in db[0].servers;
        reveal_SeqIsUnique();
        assert SeqIsUnique(config);

        // NOW CONSTRUCT FUTURE PROTOCOL STATES
        var i := 1;
        while ( i < |db| )
            decreases |db| - i;
            invariant 1 <= i <= |db|;
            invariant i == |lb|;
            invariant LS_Init(lb[0], config); 
            invariant forall k :: 0 <= k < i ==> lb[k].environment == convertEnv(db[k].environment);
            invariant forall k :: 0 <= k < i ==> lb[k].servers == map s | s in db[k].servers :: db[k].servers[s].node;
            invariant i > 1 ==> LS_Next(lb[0], lb[1]);
            invariant forall k :: 1 < k < i ==>  LS_Next(lb[k-1], lb[k]); 
        {         
            // Create and append new LS_State
            var env := convertEnv(db[i].environment);
            var servers := map s | s in db[i].servers :: db[i].servers[s].node;
            lb := lb + [LS_State(env, servers)];
            i := i + 1;

            // Convince Dafny that LS_Next(lb[i-2], lb[i-1])
            assert forall k :: 0 <= k < |db| - 1 ==> DS_Next(db[k], db[k+1]);
            assert forall k :: 0 < k < |db| ==> 0 <= k-1 && k-1 < |db|-1; 
            assert forall k :: 0 < k < |db| ==> DS_Next(db[k-1], db[k]);
            var k := i - 1;
            assert 0 < k < |db|;
            assert DS_Next(db[k-1], db[k]);
            assert lb[i-2] == LS_State(convertEnv(db[i-2].environment), map s | s in db[i-2].servers :: db[i-2].servers[s].node);
            assert lb[i-1] == LS_State(convertEnv(db[i-1].environment), map s | s in db[i-1].servers :: db[i-1].servers[s].node);
            LS_NextGood(db[i-2], db[i-1], lb[i-2], lb[i-1]);
        }

        // FINALLY: Make sure LS_Next is true forall i, and we are done
        assert forall k :: 0 < k < |lb| ==>  LS_Next(lb[k-1], lb[k]);
        assert forall i :: 0 <= i < |lb| - 1 ==>  i+1 < |lb| && 0 < i+1;
        assert forall i :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i+1]);
    }

    /* Proof that DS_Next(s, s': DS_State) implies LS_Next(t, t': LS_State) */
    lemma LS_NextGood(ds: DS_State, ds':DS_State, ls: LS_State, ls': LS_State) 
        requires DS_Next(ds, ds');
        requires ls == LS_State(convertEnv(ds.environment), map s | s in ds.servers :: ds.servers[s].node);
        requires ls' == LS_State(convertEnv(ds'.environment), map s | s in ds'.servers :: ds'.servers[s].node);
        ensures LS_Next(ls, ls');
    {
            envNextStepGood(ds.environment, ds'.environment, ls.environment, ls'.environment);
            assert LEnvironment_Next(ls.environment, ls'.environment);
            if ls.environment.nextStep.LEnvStepHostIos? && ls.environment.nextStep.actor in ls.servers {
                assert ds.environment.nextStep.actor in ds.servers;
                assert DS_NextOneServer(ds, ds', ds.environment.nextStep.actor, ds.environment.nextStep.ios);
                LS_NextOneServerGood(
                    ds, ds', ds.environment.nextStep.actor, ds.environment.nextStep.ios,
                    ls, ls', ls.environment.nextStep.actor, ls.environment.nextStep.ios
                );                   
                assert LS_NextOneServer(ls, ls', ls.environment.nextStep.actor, ls.environment.nextStep.ios);
            } else {
                assert ls.servers == ls'.servers;
            }
            assert LS_Next(ls, ls');
    }



    /* Proof that LS_NextOneServer(ds, ds', did, dios) implies LS_NextOneServer on the 
    corresponding LS_States */
    lemma LS_NextOneServerGood(ds: DS_State, ds': DS_State, did:EndPoint, dios:seq<LIoOp<EndPoint,seq<byte>>>, 
                     ls:LS_State, ls':LS_State, lid:EndPoint, lios:seq<LockIo>) 
        requires did in ds.servers;
        requires DS_NextOneServer(ds, ds', did, dios);
        requires ds.environment.nextStep.LEnvStepHostIos? && ds.environment.nextStep.actor in ds.servers;
        requires did == ds.environment.nextStep.actor;
        requires dios == ds.environment.nextStep.ios;
        requires ls == LS_State(convertEnv(ds.environment), map s | s in ds.servers :: ds.servers[s].node);
        requires ls' == LS_State(convertEnv(ds'.environment), map s | s in ds'.servers :: ds'.servers[s].node);
        requires ls.environment.nextStep.LEnvStepHostIos? && ls.environment.nextStep.actor in ls.servers;
        requires lid == ls.environment.nextStep.actor;
        requires lios == ls.environment.nextStep.ios;
        requires did == lid;
        requires lid in ls.servers;
        ensures LS_NextOneServer(ls, ls', lid, lios);
    {
        assert lid in ls'.servers;
        assert ls'.servers == ls.servers[lid := ls'.servers[lid]];

        assert lios == convertLEnvStepHostIos(dios);
        convertLEnvStepHostIosLemma(dios, lios);

        // Prove that HostNext(ds.servers[did], ds'.servers[did], dios) implies
        // NodeNext(ls.servers[lid], ls'.servers[lid], lios);
        assert HostNext(ds.servers[did], ds'.servers[did], dios);

        var s  := ls.servers[lid];
        var s' := ls'.servers[lid];
        assert NodeNext(ds.servers[did].node, ds'.servers[did].node, AbstractifyRawLogToIos(dios));
        assert NodeNext(ls.servers[lid], ls'.servers[lid], lios);
    }


    /* Proof that LEnvironment_Next(d1, d2) ==> LEnvironment_Next(convertEnv(d1), convertEnv(d2)) */
    lemma envNextStepGood(
        d1: LEnvironment<EndPoint, seq<byte>>, 
        d2: LEnvironment<EndPoint, seq<byte>>,
        l1: LEnvironment<EndPoint, LockMessage>,
        l2: LEnvironment<EndPoint, LockMessage>
        )
        requires LEnvironment_Next(d1, d2);
        requires l1 == convertEnv(d1) && l2 == convertEnv(d2);
        ensures LEnvironment_Next(l1, l2); 
    {
        convertEnvLemma(d1, l1);
        convertEnvLemma(d2, l2);
        if l1.nextStep.LEnvStepHostIos? {
            convertNextStepLemma(d1.nextStep, l1.nextStep);
            convertLEnvStepHostIosLemma(d1.nextStep.ios, l1.nextStep.ios);
            assert LEnvironment_PerformIos(l1, l2, l1.nextStep.actor, l1.nextStep.ios); 
        }
    }


    /* Helper: Takes a DS_State environment and transforms it into a LS_State environment
    */
    lemma convertEnvLemma(e1: LEnvironment<EndPoint, seq<byte>>, e2: LEnvironment<EndPoint, LockMessage>)
        requires e2 == convertEnv(e1);
        // Ensure construction is correct
        ensures e2.time == e1.time;
        ensures e2.sentPackets == set p | p in e1.sentPackets :: LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)));
        ensures e2.hostInfo == convertHostInfo(e1.hostInfo);
        ensures e2.nextStep == convertNextStep(e1.nextStep);
        
        // Ensure predicates are maintained
        ensures LEnvironment_Init(e1) ==> LEnvironment_Init(e2);
        ensures IsValidLEnvStep(e1, e1.nextStep) ==> IsValidLEnvStep(e2, e2.nextStep);

    {
        convertHostInfoLemma(e1.hostInfo, e2.hostInfo);
        if IsValidLEnvStep(e1, e1.nextStep) && e1.nextStep.LEnvStepHostIos? {
            assert LIoOpSeqCompatibleWithReduction(e1.nextStep.ios);
            convertLEnvStepHostIosLemma(e1.nextStep.ios, e2.nextStep.ios);
        }
        convertNextStepLemma(e1.nextStep, e2.nextStep);

        assert IsValidLEnvStep(e1, e1.nextStep) && e2.nextStep.LEnvStepHostIos? ==> (
            forall i :: 0<= i < |e2.nextStep.ios| ==> (
                IsValidLIoOp(e1.nextStep.ios[i], e1.nextStep.actor, e1)
            )
        );
        assert IsValidLEnvStep(e1, e1.nextStep) && e2.nextStep.LEnvStepHostIos? ==> IsValidLEnvStep(e2, e2.nextStep);
    }

    function convertEnv(e1: LEnvironment<EndPoint, seq<byte>>) : LEnvironment<EndPoint, LockMessage> {
        LEnvironment(e1.time,
                    set p | p in e1.sentPackets :: LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg))),
                    convertHostInfo(e1.hostInfo),
                    convertNextStep(e1.nextStep))        
    }

    
    /* Proof: Prove that convertNextStep function is correct */
    lemma convertNextStepLemma(ns1: LEnvStep<EndPoint, seq<byte>>, ns2: LEnvStep<EndPoint, LockMessage>) 
        requires ns2 == convertNextStep(ns1);
        ensures match ns1
            case LEnvStepHostIos(actor, ios)    => 
                ns2 == LEnvStepHostIos(actor, convertLEnvStepHostIos(ios))
            case LEnvStepDeliverPacket(p)       => 
                ns2 == LEnvStepDeliverPacket(LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg))))
            case LEnvStepAdvanceTime            => 
                ns2 == LEnvStepAdvanceTime()
            case LEnvStepStutter                => 
                ns2 == LEnvStepStutter()
    {}


    /* Helper: Takes a LEnvStep<EndPoint, seq<byte>> belonging to a ds state and 
    * returns a corresponding LEnvStep<EndPoint, LockMessage> belonging 
    * to a ls state */
    function convertNextStep(ns: LEnvStep<EndPoint, seq<byte>>) : LEnvStep<EndPoint, LockMessage> {
        match ns
            case LEnvStepHostIos(actor, ios)    => 
                LEnvStepHostIos(actor, convertLEnvStepHostIos(ios))
            case LEnvStepDeliverPacket(p)       => 
                LEnvStepDeliverPacket(LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg))))
            case LEnvStepAdvanceTime            => 
                LEnvStepAdvanceTime()
            case LEnvStepStutter                => 
                LEnvStepStutter()
    }


    /* Proof: Prove that convertLEnvStepHostIos function is correct */
    lemma convertLEnvStepHostIosLemma(s1: seq<LIoOp<EndPoint, seq<byte>>>, s2: seq<LIoOp<EndPoint, LockMessage>>)
        requires s2 == convertLEnvStepHostIos(s1);
        ensures |s1| == |s2|;
        ensures forall i :: 0 <= i < |s1| ==> (
            match s1[i] 
            case LIoOpSend(s)               =>
                s2[i] == LIoOpSend(LPacket(s.dst, s.src, AbstractifyCMessage(DemarshallData(s.msg))))
            case LIoOpReceive(r)            =>
                s2[i] == LIoOpReceive(LPacket(r.dst, r.src, AbstractifyCMessage(DemarshallData(r.msg))))
            case LIoOpTimeoutReceive()      =>
                s2[i] == LIoOpTimeoutReceive()
            case LIoOpReadClock(t)          =>
                s2[i] == LIoOpReadClock(t)
        );

        // Some nice properties
        ensures LIoOpSeqCompatibleWithReduction(s1) ==> LIoOpSeqCompatibleWithReduction(s2);
    {
        if |s1| == 0 {
            assert |s2| == 0;
        } else {
            convertLEnvStepHostIosLemma(s1[1..], s2[1..]);
        }
    }

    /* Helper: Takes a seq<LIoOp<EndPoint, seq<byte>>> belonging to a ds state and 
    * returns a corresponding seq<LIoOp<EndPoint, LockMessage>> belonging 
    * to a ls state */
    function convertLEnvStepHostIos(s1: seq<LIoOp<EndPoint, seq<byte>>>) : seq<LIoOp<EndPoint, LockMessage>> {
        if |s1| == 0 then [] else
        match s1[0] 
            case LIoOpSend(s)               =>
                [LIoOpSend(LPacket(s.dst, s.src, AbstractifyCMessage(DemarshallData(s.msg))))] + convertLEnvStepHostIos(s1[1..])
            case LIoOpReceive(r)            =>
                [LIoOpReceive(LPacket(r.dst, r.src, AbstractifyCMessage(DemarshallData(r.msg))))] + convertLEnvStepHostIos(s1[1..])
            case LIoOpTimeoutReceive()      =>
                [LIoOpTimeoutReceive()] + convertLEnvStepHostIos(s1[1..])
            case LIoOpReadClock(t)          =>
                [LIoOpReadClock(t)] + convertLEnvStepHostIos(s1[1..])
    }


    /* Proof: Prove that byteSeqToLockMessageSeq function is correct */
    lemma byteSeqToLockMessageSeqLemma(byte_seq:seq<LPacket<EndPoint, seq<byte>>>, lock_msg_seq:seq<LPacket<EndPoint, LockMessage>>)
        requires lock_msg_seq == byteSeqToLockMessageSeq(byte_seq);
        ensures |byte_seq| == |lock_msg_seq|;
        ensures forall i :: 0 <= i < |byte_seq| ==> byte_seq[i].dst == lock_msg_seq[i].dst;
        ensures forall i :: 0 <= i < |byte_seq| ==> byte_seq[i].src == lock_msg_seq[i].src;
        ensures forall i :: 0 <= i < |byte_seq| ==> AbstractifyCMessage(DemarshallData(byte_seq[i].msg)) == lock_msg_seq[i].msg;
    {
        if (|byte_seq| == 0) {
            assert |lock_msg_seq| == 0;
        } else {
            byteSeqToLockMessageSeqLemma(byte_seq[1..], lock_msg_seq[1..]);
        }
    }

    /* Helper: Takes a seq<LPacket<EndPoint, seq<byte>>> belonging to a ds state and 
    * returns a corresponding seq<LPacket<EndPoint, LockMessage>> belonging 
    * to a ls state */
    function byteSeqToLockMessageSeq(byte_seq:seq<LPacket<EndPoint, seq<byte>>>) : seq<LPacket<EndPoint, LockMessage>> 
    {
        if (|byte_seq| == 0) then
            []
        else
            [LPacket(byte_seq[0].dst, byte_seq[0].src, AbstractifyCMessage(DemarshallData(byte_seq[0].msg)))] + byteSeqToLockMessageSeq(byte_seq[1..])
    }

    /* Proof: Prove that convertHostInfo function is correct */
    lemma convertHostInfoLemma(h1: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>, h2: map<EndPoint, LHostInfo<EndPoint, LockMessage>>)
        requires h2 == convertHostInfo(h1);
        ensures forall ep :: ep in h1 <==> ep in h2;
        ensures |h1| == |h2|; 
        ensures forall ep :: ep in h2 ==> h2[ep].queue == byteSeqToLockMessageSeq(h1[ep].queue); 
    {
        if |h1| == 0 {
            assert |h2| == |h1|;
        } else {
            var k :| k in h1;
            assert k in h2;
            var h1' := map ep | ep in h1 && ep != k :: h1[ep];
            var h2' := map ep | ep in h2 && ep != k :: h2[ep];
            assert h1'.Keys == h1.Keys - {k};
            assert h2'.Keys == h2.Keys - {k};
            assert |h1'.Keys| == |h1.Keys| - 1;
            assert |h2'.Keys| == |h2.Keys| - 1;
            convertHostInfoLemma(h1', h2');
        }
    }

    function convertHostInfo(h1: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>) : map<EndPoint, LHostInfo<EndPoint, LockMessage>> {
        map ep : EndPoint | ep in h1 :: LHostInfo(byteSeqToLockMessageSeq(h1[ep].queue))
    }



    /*************************************************************************************
    * Prove that the protocol conforms to the spec
    *************************************************************************************/

    lemma augmentLS(config:ConcreteConfiguration, lb:seq<LS_State>) returns (glb: seq<GLS_State>) 
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires |lb| > 0;
        requires LS_Init(lb[0], config);
        requires forall i :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i+1]);
        ensures  |lb| == |glb|; 
        ensures  GLS_Init(glb[0], config); 
        ensures  forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
    {}

    
    lemma ProtocolToSpec(config:ConcreteConfiguration, glb:seq<GLS_State>) returns (sb:seq<ServiceState>)
        // requires |glb| > 0;
        // requires GLS_Init(glb[0], config);
        // requires forall i :: 0 <= i < |lb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
        // ensures  |glb| == |sb|;
        // ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(glb[0].ls.servers));
        // ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        // ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {

    }
}
