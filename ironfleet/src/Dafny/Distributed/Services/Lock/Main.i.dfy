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
        reveal_abstractifyPacket();
        var lb := ImplToProtocol(config, db);   // DS to LS
        var glb := augmentLS(config, lb);       // LS to GLS
        sb := protocolToSpec(config, glb);      // GLS to SS
    }


    /*************************************************************************************
    * Prove that the implementation conforms to the protocol
    *************************************************************************************/

 
    /* Takes a sequence of implementation states and returns a corresponding sequence of 
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
        // ensures  forall i :: 0 <= i < |lb| ==> lb[i].environment.sentPackets == abstractifySentPackets(db[i].environment.sentPackets);
        ensures  forall i :: 0 <= i < |lb| ==> Service_Correspondence_DB_to_LS(db[i].environment.sentPackets, lb[i].environment.sentPackets);
    {
        reveal_convertEnv();
        reveal_abstractifySentPackets();
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
            // invariant forall k :: 0 <= k < i ==> lb[k].environment.sentPackets == abstractifySentPackets(db[k].environment.sentPackets);
            invariant i > 1 ==> LS_Next(lb[0], lb[1]);
            invariant forall k :: 1 < k < i ==>  LS_Next(lb[k-1], lb[k]); 
        {         
            // Create and append new LS_State
            var env := convertEnv(db[i].environment);
            var servers := map s | s in db[i].servers :: db[i].servers[s].node;
            lb := lb + [LS_State(env, servers)];
            assert lb[i].servers == map s | s in db[i].servers :: db[i].servers[s].node;
            i := i + 1;

            // Convince Dafny that LS_Next(lb[i-2], lb[i-1])
            assert forall k :: 0 <= k < |db| - 1 ==> DS_Next(db[k], db[k+1]);
            assert forall k :: 0 < k < |db| ==> 0 <= k-1 && k-1 < |db|-1; 
            assert forall k :: 0 < k < |db| ==> DS_Next(db[k-1], db[k]);
            var k := i - 1;
            assert 0 < k < |db|;
            assert DS_Next(db[k-1], db[k]);
            assert lb[k-1] == LS_State(convertEnv(db[k-1].environment), map s | s in db[k-1].servers :: db[k-1].servers[s].node);
            assert lb[k] == LS_State(convertEnv(db[k].environment), map s | s in db[k].servers :: db[k].servers[s].node);
            LS_NextGood(db[k-1], db[k], lb[k-1], lb[k]);
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
        reveal_convertEnv();
        reveal_convertNextStep();
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
        reveal_convertEnv();
        reveal_convertNextStep();
        reveal_abstractifyPacket();
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
        reveal_abstractifySentPackets();
        reveal_convertEnv();
        reveal_convertNextStep();
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
        ensures e2.sentPackets == abstractifySentPackets(e1.sentPackets);
        ensures e2.hostInfo == convertHostInfo(e1.hostInfo);
        ensures e2.nextStep == convertNextStep(e1.nextStep);
        
        // Ensure predicates are maintained
        ensures LEnvironment_Init(e1) ==> LEnvironment_Init(e2);
        ensures IsValidLEnvStep(e1, e1.nextStep) ==> IsValidLEnvStep(e2, e2.nextStep);

    {
        reveal_convertEnv();
        reveal_convertNextStep();
        reveal_abstractifyPacket();
        reveal_abstractifySentPackets();
        convertHostInfoLemma(e1.hostInfo, e2.hostInfo);
        if IsValidLEnvStep(e1, e1.nextStep) && e1.nextStep.LEnvStepHostIos? {
            assert LIoOpSeqCompatibleWithReduction(e1.nextStep.ios);
            convertLEnvStepHostIosLemma(e1.nextStep.ios, e2.nextStep.ios);
        }
        convertNextStepLemma(e1.nextStep, e2.nextStep);
        abstractifySentPacketsLemma(e1.sentPackets, e2.sentPackets);

        assert IsValidLEnvStep(e1, e1.nextStep) && e2.nextStep.LEnvStepHostIos? ==> (
            forall i :: 0<= i < |e2.nextStep.ios| ==> (
                IsValidLIoOp(e1.nextStep.ios[i], e1.nextStep.actor, e1)
            )
        );
        assert IsValidLEnvStep(e1, e1.nextStep) && e2.nextStep.LEnvStepHostIos? ==> IsValidLEnvStep(e2, e2.nextStep);
    }

    function {:opaque} convertEnv(e1: LEnvironment<EndPoint, seq<byte>>) : LEnvironment<EndPoint, LockMessage> {
        LEnvironment(e1.time,
                    abstractifySentPackets(e1.sentPackets),
                    convertHostInfo(e1.hostInfo),
                    convertNextStep(e1.nextStep))        
    }


    /* Proof that abstractifySentPackets preserves the appropriate properties */
    lemma abstractifySentPacketsLemma(sp: set<LPacket<EndPoint, seq<byte>>>, sp': set<LPacket<EndPoint, LockMessage>>) 
        requires sp' == abstractifySentPackets(sp);
        ensures forall p :: p in sp ==> abstractifyPacket(p) in sp'
    {
        reveal_abstractifySentPackets();
    }


    /* Helper: Convert set<LPacket<EndPoint, seq<byte>> to set<LPacket<EndPoint, LockMessage> */
    function {:opaque} abstractifySentPackets(sp: set<LPacket<EndPoint, seq<byte>>>) : set<LPacket<EndPoint, LockMessage>>
    {
        set p | p in sp :: abstractifyPacket(p)
    }
    
    /* Helper: Convert LPacket<EndPoint, seq<byte> to LPacket<EndPoint, LockMessage */
    function {:opaque} abstractifyPacket(p: LPacket<EndPoint, seq<byte>>) : LPacket<EndPoint, LockMessage>
    {
        LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)))
    }

    
    /* Proof: Prove that convertNextStep function is correct */
    lemma convertNextStepLemma(ns1: LEnvStep<EndPoint, seq<byte>>, ns2: LEnvStep<EndPoint, LockMessage>) 
        requires ns2 == convertNextStep(ns1);
        ensures match ns1
            case LEnvStepHostIos(actor, ios)    => 
                ns2 == LEnvStepHostIos(actor, convertLEnvStepHostIos(ios))
            case LEnvStepDeliverPacket(p)       => 
                ns2 == LEnvStepDeliverPacket(abstractifyPacket(p))
            case LEnvStepAdvanceTime            => 
                ns2 == LEnvStepAdvanceTime()
            case LEnvStepStutter                => 
                ns2 == LEnvStepStutter()
    {
        reveal_convertNextStep();
    }


    /* Helper: Takes a LEnvStep<EndPoint, seq<byte>> belonging to a ds state and 
    * returns a corresponding LEnvStep<EndPoint, LockMessage> belonging 
    * to a ls state */
    function {:opaque} convertNextStep(ns: LEnvStep<EndPoint, seq<byte>>) : LEnvStep<EndPoint, LockMessage> {
        match ns
            case LEnvStepHostIos(actor, ios)    => 
                LEnvStepHostIos(actor, convertLEnvStepHostIos(ios))
            case LEnvStepDeliverPacket(p)       => 
                LEnvStepDeliverPacket(abstractifyPacket(p))
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
                s2[i] == LIoOpSend(abstractifyPacket(s))
            case LIoOpReceive(r)            =>
                s2[i] == LIoOpReceive(abstractifyPacket(r))
            case LIoOpTimeoutReceive()      =>
                s2[i] == LIoOpTimeoutReceive()
            case LIoOpReadClock(t)          =>
                s2[i] == LIoOpReadClock(t)
        );

        // Some nice properties
        ensures LIoOpSeqCompatibleWithReduction(s1) ==> LIoOpSeqCompatibleWithReduction(s2);
    {
        reveal_convertLEnvStepHostIos();
        if |s1| == 0 {
            assert |s2| == 0;
        } else {
            convertLEnvStepHostIosLemma(s1[1..], s2[1..]);
        }
    }

    /* Helper: Takes a seq<LIoOp<EndPoint, seq<byte>>> belonging to a ds state and 
    * returns a corresponding seq<LIoOp<EndPoint, LockMessage>> belonging 
    * to a ls state */
    function {:opaque} convertLEnvStepHostIos(s1: seq<LIoOp<EndPoint, seq<byte>>>) : seq<LIoOp<EndPoint, LockMessage>> {
        if |s1| == 0 then [] else
        match s1[0] 
            case LIoOpSend(s)               =>
                [LIoOpSend(abstractifyPacket(s))] + convertLEnvStepHostIos(s1[1..])
            case LIoOpReceive(r)            =>
                [LIoOpReceive(abstractifyPacket(r))] + convertLEnvStepHostIos(s1[1..])
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
        reveal_abstractifyPacket();
        reveal_byteSeqToLockMessageSeq();
        if (|byte_seq| == 0) {
            assert |lock_msg_seq| == 0;
        } else {
            byteSeqToLockMessageSeqLemma(byte_seq[1..], lock_msg_seq[1..]);
        }
    }

    /* Helper: Takes a seq<LPacket<EndPoint, seq<byte>>> belonging to a ds state and 
    * returns a corresponding seq<LPacket<EndPoint, LockMessage>> belonging 
    * to a ls state */
    function {:opaque} byteSeqToLockMessageSeq(byte_seq:seq<LPacket<EndPoint, seq<byte>>>) : seq<LPacket<EndPoint, LockMessage>> 
    {
        if (|byte_seq| == 0) then
            []
        else
            [abstractifyPacket(byte_seq[0])] + byteSeqToLockMessageSeq(byte_seq[1..])
    }

    /* Proof: Prove that convertHostInfo function is correct */
    lemma convertHostInfoLemma(h1: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>, h2: map<EndPoint, LHostInfo<EndPoint, LockMessage>>)
        requires h2 == convertHostInfo(h1);
        ensures forall ep :: ep in h1 <==> ep in h2;
        ensures |h1| == |h2|; 
        ensures forall ep :: ep in h2 ==> h2[ep].queue == byteSeqToLockMessageSeq(h1[ep].queue); 
    {
        reveal_convertHostInfo();
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

    function {:opaque} convertHostInfo(h1: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>) : map<EndPoint, LHostInfo<EndPoint, LockMessage>> {
        map ep : EndPoint | ep in h1 :: LHostInfo(byteSeqToLockMessageSeq(h1[ep].queue))
    }



    /*************************************************************************************
    * Prove that the protocol conforms to the spec
    *************************************************************************************/

    /* Takes a sequence of LS_States states and returns a corresponding sequence of GLS_States
    */
    lemma augmentLS(config:ConcreteConfiguration, lb:seq<LS_State>) returns (glb: seq<GLS_State>) 
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires |lb| > 0;
        requires LS_Init(lb[0], config);
        requires forall i :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i+1]);
        ensures  |lb| == |glb|; 
        ensures  GLS_Init(glb[0], config); 
        ensures  forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
        ensures  forall i :: 0 <= i < |glb| ==> Service_Correspondence_LS_to_GLS(lb[i].environment.sentPackets, glb[i].ls.environment.sentPackets);
    {   
        var history := [config[0]];
        glb := [GLS_State(lb[0], history)];

        var i := 1;
        while (i < |lb|) 
            decreases |lb| - i;
            invariant |glb| == i;
            invariant 1 <= i <= |lb|;
            invariant GLS_Init(glb[0], config);
            invariant i < |lb| ==> LS_Next(lb[i-1], lb[i]); 
            invariant forall k :: 0 <= k < i ==> glb[k].ls == lb[k]; 
            invariant forall k :: 0 < k < i ==>  GLS_Next(glb[k-1], glb[k]); 
            invariant history == glb[i-1].history; 
        {
            var s' := lb[i];
            var s := lb[i-1];
            if (s.environment.nextStep.LEnvStepHostIos? 
                && s.environment.nextStep.actor in s.servers
                && NodeGrant(s.servers[s.environment.nextStep.actor], s'.servers[s.environment.nextStep.actor], s.environment.nextStep.ios)
                && s.servers[s.environment.nextStep.actor].held && s.servers[s.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF)
            {
                history := history + [s.servers[s.environment.nextStep.actor].config[(s.servers[s.environment.nextStep.actor].my_index + 1) % |s.servers[s.environment.nextStep.actor].config|]];
                glb := glb + [GLS_State(lb[i], history)];
                assert history == glb[i-1].history + [s.servers[s.environment.nextStep.actor].config[(s.servers[s.environment.nextStep.actor].my_index + 1) % |s.servers[s.environment.nextStep.actor].config|]];
                assert glb[i].history == history;
            } else {
                history := history;
                glb := glb + [GLS_State(lb[i], history)];
                assert history == glb[i-1].history;
                assert glb[i].history == glb[i-1].history;
            }
            assert glb[i-1].ls == lb[i-1] && glb[i].ls == lb[i];
            assert LS_Next(glb[i-1].ls, glb[i].ls);
            assert GLS_Next(glb[i-1], glb[i]);
            i := i + 1;
        }
        assert forall k :: 0 < k < |glb| ==>  GLS_Next(glb[k-1], glb[k]); 
        assert forall i :: 0 <= i < |glb|-1 ==> 0 < i+1 && i+1 < |glb|;
        assert forall i :: 0 <= i < |glb|-1 ==>  GLS_Next(glb[i], glb[i+1]);
    }

    /* Takes a sequence of GLS_States states and returns a corresponding sequence of Service_States
    */
    lemma protocolToSpec(config:ConcreteConfiguration, glb:seq<GLS_State>) returns (sb:seq<ServiceState>)
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
        ensures  |glb| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(glb[0].ls.servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |glb| ==> Service_Correspondence_GLS_to_SS(glb[i].ls.environment.sentPackets, sb[i]);
    {
        sb := [];
        var i := 0;
        serverInvariantGLS(glb);
        configInvariantGLS(glb);
        assert forall ep :: ep in config <==> ep in glb[0].ls.servers;
        assert forall ep :: ep in glb[i].ls.servers ==> (
            glb[0].ls.servers[ep].config == config
        );
        while (i < |glb|) 
            decreases |glb| - i;
            invariant 0 <= i <= |glb|;
            invariant forall k :: 0 <= k < i ==> (
                forall ep :: ep in config <==> ep in glb[k].ls.servers
            );
            invariant forall k :: 0 <= k < i ==> (
                forall ep :: ep in glb[k].ls.servers ==> (
                    glb[k].ls.servers[ep].config == config
                )
            );
            invariant |sb| == i;
            invariant forall k :: 0 <= k < i ==> sb[k] == GLS_to_Spec(glb[k]);
            invariant forall k :: 0 < k < i ==> sb[k-1] == sb[k] || Service_Next(sb[k-1], sb[k]);

            // Stuff for proving Service_Correspondence 
            invariant forall k :: 0 <= k < i ==> Service_Invariant(glb[k], sb[k]);
            invariant forall k :: 0 <= k < i ==> Service_Correspondence_GLS_to_SS(glb[k].ls.environment.sentPackets, sb[k])
        {
            sb := sb + [GLS_to_Spec(glb[i])];
            assert GLS_Init(glb[0], config);
            assert LS_Init(glb[0].ls, config);
            GLS2SpecCorrect(glb[0], sb[0], config);
            if i > 0 {
                assert forall k :: 0 <= k < |glb| - 1 ==>  GLS_Next(glb[k], glb[k+1]);
                assert 0 <= i-1 < |glb| - 1;
                assert GLS_Next(glb[i-1], glb[i]);
                serviceNextGood(glb[i-1], glb[i], sb[i-1], sb[i], config);
                assert sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
                GLS2SpecCorrect(glb[i], sb[i], config);

                // Stuff for proving Service_Correspondence
                assert Service_Invariant(glb[i-1], sb[i-1]);
                Service_Invariant_Correct(glb[i-1], sb[i-1]);
                serviceInduction(glb[i-1], sb[i-1], glb[i], sb[i]);
                assert Service_Invariant(glb[i], sb[i]);
                Service_Invariant_Correct(glb[i], sb[i]);
                assert Service_Correspondence_GLS_to_SS(glb[i].ls.environment.sentPackets, sb[i]);
            }
            i := i + 1;
        }
        assert GLS_Init(glb[0], config);
        assert sb[0] == GLS_to_Spec(glb[0]);
        GLS2SpecCorrect(glb[0], sb[0], config);
        assert forall k :: 0 < k < |sb| ==> sb[k-1] == sb[k] || Service_Next(sb[k-1], sb[k]);
        assert forall i :: 0 <= i < |sb| - 1 ==> 0 < i+1 < |sb|;
        assert forall i :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
    }


    /* Proof that for any sequence of consecutive GLS_States, the config of every node in
    * the server maps are the same */
    lemma configInvariantGLS(glb:seq<GLS_State>)
        requires |glb| > 0;
        requires forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
        requires forall i :: 0 <= i < |glb| ==> glb[i].ls.servers.Keys == glb[0].ls.servers.Keys;
        ensures forall i :: 0 <= i < |glb| ==> (
            forall ep :: ep in glb[i].ls.servers ==> (
                glb[i].ls.servers[ep].config == glb[0].ls.servers[ep].config
            )
        );
    {
        if (|glb| > 1) {
            GLS_NextConfigInvarint(glb[0], glb[1]);
            var tail := glb[1..];
            assert forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
            assert forall i :: 0 <= i < |tail| - 1 ==> tail[i] == glb[i+1];
            assert forall i :: 0 <= i < |tail| - 1 ==> 1 <= i+1 < |glb| - 1;
            assert forall i :: 0 <= i < |tail| - 1 ==>  GLS_Next(tail[i], tail[i+1]);
            configInvariantGLS(tail);
        }
    }

    /* Proof that for two neighboring GLS_States, the config of every node in
    * the server maps are the same */
    lemma GLS_NextConfigInvarint(gls: GLS_State, gls': GLS_State)
        requires GLS_Next(gls, gls');
        requires gls.ls.servers.Keys == gls'.ls.servers.Keys;
        ensures forall ep :: ep in gls.ls.servers ==> (
            gls.ls.servers[ep].config == gls'.ls.servers[ep].config
        );
    {}


    /* Proof that for any sequence of consecutive GLS_States, the domains of their respective server
    * maps are the same */
    lemma serverInvariantGLS(glb:seq<GLS_State>)
        requires |glb| > 0;
        requires forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
        ensures forall i :: 0 <= i < |glb| ==> glb[i].ls.servers.Keys == glb[0].ls.servers.Keys;
    {
        if (|glb| > 1) {
            GLS_NextServerInvarint(glb[0], glb[1]);
            var tail := glb[1..];
            assert forall i :: 0 <= i < |glb| - 1 ==>  GLS_Next(glb[i], glb[i+1]);
            assert forall i :: 0 <= i < |tail| - 1 ==> tail[i] == glb[i+1];
            assert forall i :: 0 <= i < |tail| - 1 ==> 1 <= i+1 < |glb| - 1;
            assert forall i :: 0 <= i < |tail| - 1 ==>  GLS_Next(tail[i], tail[i+1]);
            serverInvariantGLS(tail);
        }
    }

    /* Proof that for two neighboring GLS_States, the domains of their respective server
    * maps are the same */
    lemma GLS_NextServerInvarint(gls: GLS_State, gls': GLS_State)
        requires GLS_Next(gls, gls');
        ensures gls.ls.servers.Keys == gls'.ls.servers.Keys
    {}


    /* Proof that GLS_Next(gls, gls') implies Service_Next(ss, ss') */
    lemma serviceNextGood(gls: GLS_State, gls': GLS_State, ss: ServiceState', ss': ServiceState', config: ConcreteConfiguration) 
        requires GLS_Next(gls, gls');
        requires ss == GLS_to_Spec(gls) && ss' == GLS_to_Spec(gls');
        requires forall ep :: ep in config <==> ep in gls.ls.servers.Keys;
        requires forall ep :: ep in config <==> ep in gls'.ls.servers.Keys;
        requires forall ep :: ep in gls.ls.servers ==> (
            gls.ls.servers[ep].config == config
        );
        requires forall ep :: ep in gls'.ls.servers ==> (
            gls'.ls.servers[ep].config == config
        );
        ensures ss == ss' || Service_Next(ss, ss');
    {
        reveal_GLS_to_Spec();
        if ss != ss' {
            assert ss.hosts == ss'.hosts;
            var lock_holder := gls.ls.servers[gls.ls.environment.nextStep.actor].config[(gls.ls.servers[gls.ls.environment.nextStep.actor].my_index + 1) % |gls.ls.servers[gls.ls.environment.nextStep.actor].config|];
            assert ss'.history == ss.history + [lock_holder];
            assert lock_holder in gls.ls.servers[gls.ls.environment.nextStep.actor].config;
            assert lock_holder in gls.ls.servers;  
            assert ss.hosts == Collections__Maps2_s.mapdomain(gls.ls.servers);
            assert lock_holder in ss.hosts;
            assert Service_Next(ss, ss');
        }
    }


    lemma GLS2SpecCorrect(gls: GLS_State, ss: ServiceState', config: ConcreteConfiguration) 
        requires |config| > 0;
        requires SeqIsUnique(config);
        requires ss == GLS_to_Spec(gls);
        ensures ss.history == gls.history;
        ensures ss.hosts == Collections__Maps2_s.mapdomain(gls.ls.servers);
        ensures GLS_Init(gls, config) ==> Service_Init(ss, Collections__Maps2_s.mapdomain(gls.ls.servers));
    {
        reveal_GLS_to_Spec();
    }

    /* Helper: Takes a GLS_State and returns a corresponding ServiceState' */
    function {:opaque} GLS_to_Spec(gls: GLS_State) : ServiceState' {
        ServiceState'(Collections__Maps2_s.mapdomain(gls.ls.servers), gls.history)
    }


    /*************************************************************************************
    * Predicates and lemmas for proving service correspondence
    * ensures forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    *************************************************************************************/

    predicate Service_Correspondence_DB_to_LS(concretePkts:set<LPacket<EndPoint, seq<byte>>>, concretePkts':set<LPacket<EndPoint, LockMessage>>) 
    {
        concretePkts' == abstractifySentPackets(concretePkts)
        && forall p :: p in concretePkts ==> abstractifyPacket(p) in concretePkts'
    }

    predicate Service_Correspondence_LS_to_GLS(concretePkts:set<LPacket<EndPoint, LockMessage>>, concretePkts':set<LPacket<EndPoint, LockMessage>>) 
    {
        concretePkts' == concretePkts
    }

    predicate Service_Correspondence_GLS_to_SS(concretePkts:set<LPacket<EndPoint, LockMessage>>, serviceState:ServiceState) 
    {
        forall p, epoch :: 
            p in concretePkts 
            && p.src in serviceState.hosts 
            && p.dst in serviceState.hosts 
            && p.msg == AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch)))
        ==>
            1 <= epoch <= |serviceState.history|
        && p.src == serviceState.history[epoch-1]
    }

    
    /* Inductive invariant for proving Service_Correspondence */
    predicate Service_Invariant(gls: GLS_State, ss:ServiceState) 
    {
        && (forall p, epoch ::
            p in gls.ls.environment.sentPackets 
            && p.src in ss.hosts 
            && p.dst in ss.hosts 
            && p.msg == AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch)))
        ==>
            p.msg == Locked(epoch)
        )
        && (forall ep :: ep in gls.ls.servers ==>
            0 <= gls.ls.servers[ep].epoch <= 0xFFFF_FFFF_FFFF_FFFF
        )
        && Service_Correspondence_GLS_to_SS(gls.ls.environment.sentPackets, ss)
    }


    /* Proof that Service_Invariant implies Service_Correspondence */
    lemma Service_Invariant_Correct(gls: GLS_State, ss:ServiceState) 
        requires Service_Invariant(gls, ss);
        ensures Service_Correspondence_GLS_to_SS(gls.ls.environment.sentPackets, ss);
    {}


    /* True iff gls-> gls' is a NodeGrant step */
    predicate NodeGrantStep(gls: GLS_State, gls': GLS_State) 
        requires gls.ls.environment.nextStep.LEnvStepHostIos?
        requires GLS_Next(gls, gls');
    {
        GLS_NextServerInvarint(gls, gls');
        && gls.ls.environment.nextStep.actor in gls.ls.servers
        && NodeGrant(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)
        && gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.servers[gls.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
    }

    /* True iff gls-> gls' is a NodeAccept step */
    predicate NodeAcceptStep(gls: GLS_State, gls': GLS_State) 
        requires gls.ls.environment.nextStep.LEnvStepHostIos?
        requires GLS_Next(gls, gls');
    {
        GLS_NextServerInvarint(gls, gls');
        var ios := gls.ls.environment.nextStep.ios;
        && gls.ls.environment.nextStep.actor in gls.ls.servers
        && NodeAccept(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], ios)
        && !ios[0].LIoOpTimeoutReceive? 
        && !gls.ls.servers[gls.ls.environment.nextStep.actor].held
        && ios[0].r.src in gls.ls.servers[gls.ls.environment.nextStep.actor].config
        && ios[0].r.msg.Transfer? 
        && ios[0].r.msg.transfer_epoch > gls.ls.servers[gls.ls.environment.nextStep.actor].epoch
    }


    /* Proof by induction that Service_Invariant(gls, ss) on i'th state
    * implies Service_Invariant(gls', ss') on (i+1)'th state */
    lemma serviceInduction(
        gls: GLS_State, 
        ss:ServiceState,
        gls': GLS_State, 
        ss':ServiceState)
        requires GLS_Next(gls, gls');
        requires ss == GLS_to_Spec(gls);
        requires ss' == GLS_to_Spec(gls');
        requires ss == ss' || Service_Next(ss, ss');
        requires Service_Invariant(gls, ss);
        ensures Service_Invariant(gls', ss');
    {
        assert IsValidLEnvStep(gls.ls.environment, gls.ls.environment.nextStep);
        match gls.ls.environment.nextStep {
            case LEnvStepHostIos(actor, ios) => {
                if (gls.ls.environment.nextStep.actor in gls.ls.servers) {
                    if (NodeGrantStep(gls, gls')) {
                        serviceInductionNodeGrant(gls, ss, gls', ss');
                    } else if NodeAcceptStep(gls, gls') {
                        serviceInductionNodeAccept(gls, ss, gls', ss');
                    } else {
                        assert gls.ls.servers == gls.ls.servers;
                        assert Service_Invariant(gls', ss');
                    }
                } else {
                    // !(gls.ls.environment.nextStep.actor in gls.ls.servers)
                    assert gls'.ls.servers == gls.ls.servers;
                    assert LEnvironment_PerformIos(gls.ls.environment, gls'.ls.environment, actor, ios);
                    var new_packets := set io | io in ios && io.LIoOpSend? :: io.s;
                    assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + new_packets;
                    assert forall p :: p in new_packets ==> !(p.src in gls.ls.servers);
                    reveal_GLS_to_Spec();
                    assert forall p :: p in new_packets ==> !(p.src in ss.hosts);
                    assert gls'.history == gls.history;
                    assert Service_Invariant(gls', ss');
                }
            } // end case LEnvStepHostIos
            case LEnvStepDeliverPacket(p) => serviceInductionNoIO(gls, ss, gls', ss');
            case LEnvStepAdvanceTime => serviceInductionNoIO(gls, ss, gls', ss');
            case LEnvStepStutter => serviceInductionNoIO(gls, ss, gls', ss');
        } // end match
    }
    

    /* Proof by induction that Service_Invariant(gls, ss) on i'th state implies 
    * Service_Invariant(gls', ss') on (i+1)'th state, given that gls->gls' is a 
    * step that does not perform any I/O with respect to the environment */
    lemma serviceInductionNoIO(gls: GLS_State, ss:ServiceState, gls': GLS_State, ss':ServiceState)
        requires GLS_Next(gls, gls');
        requires ss == GLS_to_Spec(gls);
        requires ss' == GLS_to_Spec(gls');
        requires ss == ss' || Service_Next(ss, ss');
        requires Service_Invariant(gls, ss);
        requires !gls.ls.environment.nextStep.LEnvStepHostIos?
        ensures Service_Invariant(gls', ss');
    {   
        assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets;
        historyPreservation(gls, gls');
        reveal GLS_to_Spec();
        assert ss'.history == gls'.history;
        assert ss.history == gls.history;
        assert ss'.history == ss.history;
        assert Service_Invariant(gls', ss');
    }

    /* Helper: Proof that if gls->gls' is a step that does no I/O with the environment,
    * then gls'.history == gls.history */
    lemma historyPreservation(gls: GLS_State, gls': GLS_State) 
        requires GLS_Next(gls, gls');
        requires !gls.ls.environment.nextStep.LEnvStepHostIos?
        ensures gls'.history == gls.history;
    {}


    /* Proof by induction that Service_Invariant(gls, ss) on i'th state implies 
    * Service_Invariant(gls', ss') on (i+1)'th state, given that gls->gls' is a 
    * NodeNext step */
    lemma serviceInductionNodeAccept(
        gls: GLS_State, 
        ss:ServiceState,
        gls': GLS_State, 
        ss':ServiceState)
        requires GLS_Next(gls, gls');
        requires ss == GLS_to_Spec(gls);
        requires ss' == GLS_to_Spec(gls');
        requires ss == ss' || Service_Next(ss, ss');
        requires Service_Invariant(gls, ss);
        requires gls.ls.environment.nextStep.LEnvStepHostIos?;
        requires NodeAcceptStep(gls, gls');
        ensures Service_Invariant(gls', ss');
    {
        var src := gls.ls.environment.nextStep.actor;
        var ios := gls.ls.environment.nextStep.ios;
        assert (gls'.ls.servers[src].held    // reminder of the facts that I know at this point
                && |ios| == 2
                && ios[1].LIoOpSend?
                && ios[1].s.msg.Locked?
                && gls'.ls.servers[src].epoch == ios[0].r.msg.transfer_epoch == ios[1].s.msg.locked_epoch
        );
        // assert Service_Invariant(gls', ss');
    }


    /* Proof by induction that Service_Invariant(gls, ss) on i'th state implies 
    * Service_Invariant(gls', ss') on (i+1)'th state, given that gls->gls' is a 
    * NodeGrant step */
    lemma serviceInductionNodeGrant(
        gls: GLS_State, 
        ss:ServiceState,
        gls': GLS_State, 
        ss':ServiceState)
        requires GLS_Next(gls, gls');
        requires ss == GLS_to_Spec(gls);
        requires ss' == GLS_to_Spec(gls');
        requires ss == ss' || Service_Next(ss, ss');
        requires Service_Invariant(gls, ss);
        requires gls.ls.environment.nextStep.LEnvStepHostIos?;
        requires NodeGrantStep(gls, gls');
        ensures Service_Invariant(gls', ss');
    {
        reveal_GLS_to_Spec();
        var src := gls.ls.environment.nextStep.actor;
        var ios := gls.ls.environment.nextStep.ios;

        assert LEnvironment_PerformIos(gls.ls.environment, gls'.ls.environment, src, ios);
        assert |ios| == 1;
        assert ios[0].LIoOpSend?;
        
        var new_packet := ios[0].s;
        var dst := new_packet.dst;
        assert ss'.history == ss.history + [dst];
        assert ss'.hosts == ss.hosts;

        // Prove that new_packet has epoch 0 <= epoch < 0x1_0000_0000_0000_0000
        assert new_packet.msg.Transfer?;
        var epoch := new_packet.msg.transfer_epoch;
        assert new_packet.msg == Transfer(epoch);
        assert 0 <= gls.ls.servers[src].epoch < 0xFFFF_FFFF_FFFF_FFFF;
        assert epoch == gls.ls.servers[src].epoch + 1;
        assert 0 <= epoch <= 0xFFFF_FFFF_FFFF_FFFF;
        
        // Now we know that the set of LockedMessages are the same 
        // in gls.ls.env.sentPackets and gls'.ls.env.sentPackets.
        assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + {new_packet};
        assert forall p :: p in gls.ls.environment.sentPackets && p.msg.Locked? <==> p in gls'.ls.environment.sentPackets && p.msg.Locked?;

        // Every packet in gls' statisfying antecedent has type Locked
        newTransferPacketLemma(new_packet.msg);
        assert forall epoch :: AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch))) != new_packet.msg;
        assert forall p, epoch :: (
            && p in gls'.ls.environment.sentPackets 
            && p.src in ss'.hosts 
            && p.dst in ss'.hosts 
            && p.msg == AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch)))
            ==> 
            && p != new_packet 
            && p.msg == Locked(epoch)
        );

        // Putting it all together
        assert forall p, epoch :: (
            && p in gls'.ls.environment.sentPackets 
            && p.src in ss'.hosts 
            && p.dst in ss'.hosts
            && p.msg == AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch)))
            ==> 
            && p in gls.ls.environment.sentPackets 
            && p.src in ss.hosts 
            && p.dst in ss.hosts
            ==>
            && 1 <= epoch <= |ss.history|
            && p.src == ss.history[epoch-1]
            ==>
            && 1 <= epoch <= |ss'.history|
            && p.src == ss'.history[epoch-1]
        );
        assert Service_Correspondence_GLS_to_SS(gls'.ls.environment.sentPackets, ss);
        assert Service_Invariant(gls', ss');
    }


    /* Proof that the new Transfer message created on NodeGrant does not correspond to 
    * any AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch))) */
    lemma newTransferPacketLemma(new_packet_msg: LockMessage)
        requires new_packet_msg.Transfer?;
        requires 0 <= new_packet_msg.transfer_epoch < 0x1_0000_0000_0000_0000;
        ensures forall epoch :: AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch))) != new_packet_msg;
    {
        forall epoch | true 
        ensures (
            || AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch))) == Locked(epoch)
            || AbstractifyCMessage(DemarshallData(MarshallLockMsg(epoch))) == Invalid
        ){
            var bytes := MarshallLockMsg(epoch);
            var cmsg := DemarshallData(bytes);
            var msg := AbstractifyCMessage(cmsg);
            if (Demarshallable(bytes, CMessageGrammar())) {
                lemma_ParseMarshallLockedAbstract(bytes, epoch, msg);
                assert AbstractifyCMessage(cmsg) == Locked(epoch);
            } else {
                assert cmsg == CInvalid();
                assert AbstractifyCMessage(cmsg) == Invalid;
            }
        }
    }
}