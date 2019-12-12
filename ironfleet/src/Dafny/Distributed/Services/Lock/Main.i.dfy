include "../../Common/Framework/Main.s.dfy"
include "LockDistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"
include "../../Impl/Lock/Host.i.dfy"
include "AbstractService.s.dfy"
// include "../../Protocol/Lock/RefinementProof/Refinement.i.dfy"
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
    // import opened Refinement_i
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
        // TODO

        // First prove Service_Init()
        var history := [config[0]];

        assert forall ep :: ep in config ==> ep in MapSeqToSet(config, x=>x);
        assert Collections__Maps2_s.mapdomain(db[0].servers) == MapSeqToSet(config, x=>x);
        assert forall ep :: ep in config ==> ep in Collections__Maps2_s.mapdomain(db[0].servers);
        assert config[0] in Collections__Maps2_s.mapdomain(db[0].servers);

        sb := [ServiceState'(Collections__Maps2_s.mapdomain(db[0].servers), history)];

        assert sb[0].history == [config[0]] && config[0] in Collections__Maps2_s.mapdomain(db[0].servers);
    

        var i := 1;
        
        while (i < |db|)
            decreases |db| - i;
            invariant 0 <= i <= |db|;
            invariant |sb| == i;
            invariant forall k :: 1 <= k < |sb| ==> sb[k].hosts == Collections__Maps2_s.mapdomain(db[k].servers);

            // Stuff for proving initial state
            invariant sb[0].history == [config[0]] && config[0] in Collections__Maps2_s.mapdomain(db[0].servers);
            invariant sb[0].hosts == Collections__Maps2_s.mapdomain(db[0].servers);
        {
            var impl_state := db[i];
            var hosts := impl_state.servers.Keys;  // set of server endpoints
            var host_states := impl_state.servers.Values;  // set of node HostStates
            
            // Find node holding the lock and add to history
            var hs_set := host_states;
            while ( hs_set != {} )
                decreases hs_set;
            {
                var hs :| hs in hs_set;
                if (hs.node_impl.node.held) {
                    history := history + [hs.node_impl.localAddr];
                    break;
                }
                hs_set := hs_set - { hs };
            }
            sb := sb + [ServiceState'(hosts, history)];
            i := i + 1;
        }
        assert i == |db|;
        assert i == |sb|;
        assert sb[0].history == [config[0]] && config[0] in Collections__Maps2_s.mapdomain(db[0].servers);
    }
}