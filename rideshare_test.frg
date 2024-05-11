#lang forge/temporal
open "rideshare.frg"

//test the predicates
//test the stuff from wellformed
//liveness and soundness/safety with different procedures
//examples

pred init_pass_logic{
    all d: Driver, p: Passenger | {
        one row, col: Int | {
            (row >= 0) and (row <= 4)
            (col >= 0) and (col <= 2)
            d.location_x = row
            d.location_y = col
        }
        --passenger logic
        p.request.fulfilled = 0
        p.request.claimed = 0
    }
}

pred bad_init_logic{
    some d: Driver, p: Passenger | {
        one row, col: Int | {
            (row >= 0) and (row <= 4)
            (col >= 0) and (col <= 2)
            d.location_x = row
            d.location_y = col
        }
        p.request in d.accepted_requests 
        --passenger logic
        p.request.fulfilled = 1
        p.request.claimed = 1

        p.locationx != p.request.origin_x
        p.locationy != p.request.origin_y

    }

}

pred already_in_car{
    some d: Driver, p: Passenger | {
        p in d.passengers_in_car
    }

}

test suite for init{
    //tests valid and invalid initial states
    test expect{
        good_init:{init_pass_logic and init and wellformed} is sat
        bad_init:{bad_init_logic and init and wellformed} is unsat
        already_car: {already_in_car and init and wellformed} is unsat

    }
}

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
    //tests valid and invlade wellformed states
    test expect{
        good_req:{wellformed_request and wellformed} is sat
        bad_req:{illformed_request and wellformed} is unsat
        good_driv:{wellformed_driver and wellformed} is sat
        bad_driv:{illformed_driver and wellformed} is unsat
    }
}

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
        --ensures driver stays still
        stays_still: {some d: Driver | d_stays_still[d] and stayStill[d] and wellformed} is sat
        --ensures driver stays still when picking up passenger
        stay_still_pick: {some d: Driver, p:Passenger | stayStill[d] and pickUp[d,p] and wellformed} is sat
        --ensures driver cannot move when picking up passenger
        moves: {some d: Driver | d_stays_still[d] and moveUp[d]} is unsat
        --ensures driver and passenger stay still together
        d_still: {some d: Driver | d_stays_still[d] and p_stays_still and wellformed} is sat
    }
}

test suite for moveUp{
    --ensure specific coords are necessary to move up/cant move up if at top of board
     assert all d: Driver |
        loc_y_up[d] is necessary for moveUp[d]
    --ensure we only move up one space at a time
    test expect{
         moveUoneatatime: {
           some d: Driver | {
               moveRight[d]
               d.location_y' = add[d.location_y, 2]
           }
       } for exactly 1 Driver is unsat
       --ensures passenger stays in car and moves up with car
        pmwcUp: {some d: Driver | p_move_up_with_car[d] and moveUp[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcUp: {some d: Driver | p_not_move_up_with_car[d] and moveUp[d] and wellformed} is unsat
    }
}

test suite for moveDown{
    --ensure specific coords are necessary to move down/cant move down if at top of board
    assert all d: Driver |
        loc_y_down[d] is necessary for moveDown[d]
    --ensure we only move down one space at a time
    test expect{
         moveDoneatatime: {
           some d: Driver | {
               moveRight[d]
               d.location_y' = subtract[d.location_y, 2]
           }
       } for exactly 1 Driver is unsat
       --ensures passenger stays in car and moves down with car
        pmwcDown: {some d: Driver | p_move_down_with_car[d] and moveDown[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcDown: {some d: Driver | p_not_move_down_with_car[d] and moveDown[d] and wellformed} is unsat
    }
}

test suite for moveRight{
    --ensure specific coords are necessary to move right/cant move right if at top of board
     assert all d: Driver |
        loc_x_right[d] is necessary for moveRight[d]
    --ensure we only move right one space at a time
    test expect{
        moveRoneatatime: {
           some d: Driver | {
               moveRight[d]
               d.location_x' = add[d.location_x, 2]
           }
       } for exactly 1 Driver is unsat
        --ensures passenger stays in car and moves right with car
        pmwcRight: {some d: Driver | p_move_right_with_car[d] and moveRight[d] and wellformed and passenger_still_in_car[d]} is sat
        npmwcRight: {some d: Driver | p_not_move_right_with_car[d] and moveRight[d] and wellformed} is unsat
    }
}

test suite for moveLeft{
    --ensure specific coords are necessary to move left/cant move left if at top of board
    assert all d: Driver |
        loc_x_left[d] is necessary for moveLeft[d]
    --ensure we only move left one space at a time
    test expect{
         moveLoneatatime: {
           some d: Driver | {
               moveLeft[d]
               d.location_x' = subtract[d.location_x, 2]
           }
       } for exactly 1 Driver is unsat
       --ensures passenger stays in car and moves left with car
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
        --checks that picking up a passenger puts them in that drivers car
        pickedup: {some d: Driver, p: Passenger | pickedUp[d, p] and pickUp[d, p] and wellformed} is sat
        --ensures you cant be picked up and dropped off at same time
        notpickedup: {some d: Driver, p: Passenger | droppedOff[d,p] and pickUp[d,p]} is unsat
        --ensures you driver can only pick up at proper location
        inwrongplace_pickup: {
           some d: Driver, p: Passenger | {
               pickUp[d,p]
               d.location_x != p.request.origin_x
           }
       } for exactly 1 Driver, 1 Passenger is unsat
    }
}

//drop off
test suite for dropOff{
    test expect{
        --ensures driver can only dropoff at passengers destination
        inwrongplace: {
           some d: Driver, p: Passenger | {
               d.location_x = p.locationx
               d.location_y = p.locationy
               dropOff[d,p]
               p.locationx != p.request.destination_x
           }
       } for exactly 1 Driver, 1 Passenger is unsat
        --ensures you can't pickup and drop off at same time
        notdroppedoff: {some d: Driver, p: Passenger | pickedUp[d, p] and dropOff[d, p] and wellformed} is unsat
        --ensures passenger actually gets dropped off/leaves car at destination when dropped off
        droppedoff: {some d: Driver, p: Passenger | droppedOff[d, p] and dropOff[d,p] and wellformed} is sat
    }
}

//liveness
pred liveness[d: Driver] {
    --ensures that all requests are eventually handled
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

//Safety
--ensures there is always a move to be made (no deadlock)
pred safety[d: Driver, p: Passenger] {
	always eventually enabled[d,p]
}

test expect{
    --tests liveness and safety for each procedure we wrote (all pass for our cases)
    proc_1: {some d: Driver, p: Passenger | procedure1[d, p] and liveness[d] and safety[d, p]} is sat
    proc_2: {some d: Driver, p: Passenger | procedure2[d, p] and liveness[d] and safety[d, p]} is sat
    proc_3: {some d: Driver, p: Passenger | procedure3[d, p] and liveness[d] and safety[d, p]} is sat
    proc_4: {some d: Driver, p: Passenger | procedure4[d, p] and liveness[d] and safety[d, p]} is sat
    proc_5: {some d: Driver, p: Passenger | procedure5[d, p] and liveness[d] and safety[d, p]} is sat
}

test suite for traces {
    test expect {
        --ensures a passenger can only be in one car at once
        passenger_in_two_cars_same_time: {
           traces
           some p: Passenger | {
               some disj d1, d2: Driver | {
                    { p in d1.passengers_in_car}
                    { p in d2.passengers_in_car}
               }
              
           }
       } for exactly 2 Passenger, 2 Driver is unsat
       --ensures party size is small enough to fit in car
       too_big: {
           traces
           some p: Passenger, d: Driver | {
               p.request.party_size > d.capacity
           }
       } for exactly 1 Passenger, 1 Driver is unsat
   }
}
