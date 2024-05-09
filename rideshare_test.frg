#lang forge/temporal
open "rideshare.frg"

//test the predicates
//test the stuff from wellformed
//liveness and soundness/safety with different procedures
//examples

//below passes through next indicating comment -- commented out to run tests faster hopefully
pred loc_y_up[d: Driver]{
    d.location_y <= 2 
}
pred loc_y_down[d: Driver]{
    d.location_y >= 0
}

pred loc_x_right[d: Driver]{
    d.location_x <= 4 
}

pred loc_x_left[d: Driver]{
    d.location_x >= 0
}

test suite for moveUp{
    assert all d: Driver |
        loc_y_up[d] is necessary for moveUp[d]
}

test suite for moveDown{
    assert all d: Driver |
        loc_y_down[d] is necessary for moveDown[d]
}

pred p_move_up_with_car[d: Driver]{
     all p: d.passengers_in_car | {
        p.locationx' = p.locationx
        p.locationy' = add[p.locationy,1]
    }
}

pred p_not_move_up_with_car[d: Driver]{

     some p: d.passengers_in_car | {
        p.locationx' = p.locationx
        p.locationy' != add[p.locationy,1]
    } 
}

pred p_move_down_with_car[d: Driver]{
     all p: d.passengers_in_car | {
        p.locationx' = p.locationx
        p.locationy' = subtract[p.locationy,1]
    }
}

pred p_not_move_down_with_car[d: Driver]{

     some p: d.passengers_in_car | {
        p.locationx' = p.locationx
        p.locationy' != subtract[p.locationy,1]
    } 
}

pred p_move_right_with_car[d: Driver]{
     all p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' = add[p.locationx,1]
    }
}

pred p_not_move_right_with_car[d: Driver]{

     some p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' != add[p.locationx,1]
    } 
}

pred p_move_left_with_car[d: Driver]{
     all p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' = subtract[p.locationx,1]
    }
}

pred p_not_move_left_with_car[d: Driver]{

     some p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' != subtract[p.locationx,1]
    } 
}

pred passenger_still_in_car[d: Driver]{
    some p: Passenger | {
        p in d.passengers_in_car implies {
            p in d.passengers_in_car'
        }
    }
}

pred d_stays_still[d: Driver]{
    d.location_x' = d.location_x
    d.location_y' = d.location_y
}

pred p_stays_still{
    all p: Passenger |{
        p.locationx' = p.locationx
        p.locationy' = p.locationy
    }
}

test suite for stayStill{
    test expect{
        stays_still: {some d: Driver | d_stays_still[d] and stayStill[d] and wellformed} is sat
        moves: {some d: Driver | d_stays_still[d] and moveUp[d]} is unsat
        d_still: {some d: Driver | d_stays_still[d] and p_stays_still and wellformed} is sat
    }
}

test suite for moveUp{
     assert all d: Driver |
        loc_y_up[d] is necessary for moveUp[d]
    test expect{
        pmwcUp: {some d: Driver | p_move_up_with_car[d] and moveUp[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcUp: {some d: Driver | p_not_move_up_with_car[d] and moveUp[d] and wellformed} is unsat
    }
}

test suite for moveDown{
     assert all d: Driver |
        loc_y_down[d] is necessary for moveDown[d]
    test expect{
        pmwcDown: {some d: Driver | p_move_down_with_car[d] and moveDown[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcDown: {some d: Driver | p_not_move_down_with_car[d] and moveDown[d] and wellformed} is unsat
    }
}

test suite for moveRight{
     assert all d: Driver |
        loc_x_right[d] is necessary for moveRight[d]

    test expect{
        pmwcRight: {some d: Driver | p_move_right_with_car[d] and moveRight[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcRight: {some d: Driver | p_not_move_right_with_car[d] and moveRight[d] and wellformed} is unsat
    }
}

test suite for moveLeft{
    assert all d: Driver |
        loc_x_left[d] is necessary for moveLeft[d]

    test expect{
        pmwcLeft: {some d: Driver | p_move_left_with_car[d] and moveLeft[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcLeft: {some d: Driver | p_not_move_left_with_car[d] and moveLeft[d] and wellformed} is unsat
    }
}


//pick up
//picked up (and also NOT dropped off)
pred pickedUp[d: Driver, p: Passenger]{
    p in d.passengers_in_car
    p.request in d.accepted_requests'
}

//not picked up 
pred notPickedUp[d: Driver, p: Passenger]{
    p not in d.passengers_in_car
    p.request not in d.accepted_requests'
}

//dropped off
pred droppedOff[d: Driver, p: Passenger]{
    d.passengers_in_car' = d.passengers_in_car - p
    d.accepted_requests' = d.accepted_requests - p.request
}

test suite for pickUp{
    test expect{
        pickedup: {some d: Driver, p: Passenger | pickedUp[d, p] and pickUp[d, p] and wellformed} is sat
        notpickedup: {some d: Driver, p: Passenger | droppedOff[d,p] and pickUp[d,p]} is unsat
    }
}

//drop off
test suite for dropOff{
    test expect{
        notdroppedoff: {some d: Driver, p: Passenger | pickedUp[d, p] and dropOff[d, p] and wellformed} is unsat
        droppedoff: {some d: Driver, p: Passenger | droppedOff[d, p] and dropOff[d,p] and wellformed} is sat
    }
}
//all tests pass through dropOff test suite

//some combos of actions...see stacks

// pred unclaimed[p: Passenger]{
//     p.request.claimed = 0
// }

// pred claimed[p: Passenger]{
//     p.request.claimed = 1
// }

// pred route1[d: Driver, p: Passenger]{
//     pickUp[d, p]
//     moveLeft[d]
//     dropOff[d, p]
// }

// assert all d: Driver, p: Passenger | unclaimed[p] is necessary for route1[d, p]


//also add more to pick up and drop off
