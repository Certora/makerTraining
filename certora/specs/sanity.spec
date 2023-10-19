rule sanity(method f) filtered { f -> f.contract == currentContract } {
    env e;
    calldataarg args;
    f(e, args);
    satisfy true;
}