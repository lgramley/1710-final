#lang forge/temporal
open "rideshare.frg"

//test the predicates
//test the stuff from wellformed
//liveness and soundness

pred loc_y[d: Driver]{
    d.location_y <= 2 
}

test suite for moveUp{
    assert all d: Driver |
        loc_y[d] is sufficient for moveUpEnabled[d]
}

