#lang forge/temporal
open "rideshare.frg"

//test the predicates
//test the stuff from wellformed
//liveness and soundness/safety with different procedures
//examples

pred wellformed_request{
    some r: Request {
        r.party_size >= 0
        r.party_size <= 4

        r.origin_x >= 0
        r.origin_y >= 0
        r.origin_x <= 4
        r.origin_y <= 2
        r.destination_x >= 0
        r.destination_y >= 0
        r.destination_x <= 4
        r.destination_y <= 2


        (r.origin_x = r.destination_x) implies{
            r.origin_y != r.destination_y
            }

        r in RequestsList.all_requests
        }
}

pred illformed_request{
    some r: Request {
        r.party_size >= 0
        r.party_size <= 4

        r.origin_x <= 0
        r.origin_y <= 0
        r.origin_x >= 4
        r.origin_y >= 2
        r.destination_x >= 0
        r.destination_y >= 0
        r.destination_x <= 4
        r.destination_y <= 2
    }
}

pred wellformed_driver{
    all d: Driver | {
        d.capacity <= 4 
        d.capacity >= 0
    }
}

pred illformed_driver{
    some d: Driver | {
        d.capacity = 6
    }
}
test suite for wellformed{
    test expect{
        good_req:{wellformed_request and wellformed} is sat
        bad_req:{illformed_request and wellformed} is unsat
        good_driv:{wellformed_driver and wellformed} is sat
        bad_driv:{illformed_driver and wellformed} is unsat
    }
}

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

//also add more to pick up and drop off

//liveness
//soundness/safety
pred liveness[d: Driver] {
	always {
		all p: Passenger | {
            (p.request in RequestsList.all_requests) => eventually (p.request in d.accepted_requests)
		}
	}
}

pred enabled[d: Driver, p: Passenger] {
    pickUpEnabled[d, p] or 
    moveLeftEnabled[d] or
    moveRightEnabled[d] or
    moveUpEnabled[d] or
    moveDownEnabled[d]
}

// Property: Safety, or the fact that the elevator can always become enabled (no deadlock)
// This property holds for procedures 1, 2, 3, 4, and 5
pred safety[d: Driver, p: Passenger] {
	always eventually enabled[d,p]
}

//liveness and safety of procedures??

test expect{
    proc_1: {some d: Driver, p: Passenger | procedure1[d, p] and liveness[d] and safety[d, p]} is sat
    proc_2: {some d: Driver, p: Passenger | procedure2[d, p] and liveness[d] and safety[d, p]} is sat
    proc_3: {some d: Driver, p: Passenger | procedure3[d, p] and liveness[d] and safety[d, p]} is sat
    proc_4: {some d: Driver, p: Passenger | procedure4[d, p] and liveness[d] and safety[d, p]} is sat
    proc_5: {some d: Driver, p: Passenger | procedure5[d, p] and liveness[d] and safety[d, p]} is sat
}