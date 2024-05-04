#lang forge/temporal
option max_tracelength 25
option min_tracelength 10

--Sigs--
sig Request {
    party_size: one Int,
    var fulfilled: one Int, //(0 , 1)
    var claimed: one Int, 
    origin_x: one Int,
    origin_y: one Int,
    destination_x: one Int,
    destination_y: one Int
}


sig Passenger {
    request: one Request
}

sig Driver {
    capacity: one Int,
    var accepted_requests: set Request,
    var current_request: one Request,
    var next_request: one Request,
    var location_x: lone Int,
    var location_y: lone Int,
    var passengers_in_car: set Passenger
}

--RequestList (global list of requests)
one sig RequestsList{
    var all_requests: set Request
}

one sig Board {
    var pos_driver : pfunc Int -> Int -> Driver, // (int, int) -> thing
    var pos_pass : pfunc Int -> Int -> Passenger
}

pred wellformed_map {
  // Fill in this predicate to ensure that:
  // The board is 5x3, so Int ranges from 0-4 and 0-2

-- BLOCK out middle squares (1, 1) and (3, 1)

  all row, col: Int | {
    (row < 0 or row > 4 or col < 0 or col > 2 or (row = 1 and col = 1) or (row = 3 and col = 1)) implies {
        no Board.pos_driver[row][col]
        no Board.pos_pass[row][col]
    }
  }

  all d: Driver | {
    one row, col: Int | {
        Board.pos_driver[row][col] = d
        d.location_x = row
        d.location_y = col
    }
  }

  all p: Passenger | {
    one row, col: Int | {
        Board.pos_pass[row][col] = p
    }
  }
} 

//Todo:
-- GOAL: car moves in a direction (ideally towards a passenger)
-- start with one car and passenger and then build up to a whole network of cars and passengers

//init: (initial state)
-- Passengers and Cars relatively spread out across the board
pred init{
    --first iteration 

    --location of car inside of driver
    --no drivers on same tile as passenger for movement purposes    
    -- cars at origin 

    all d: Driver, p: Passenger | {
        one row, col: Int | {
        (row >= 0) and (row <= 4)
        (col >= 0) and (col <= 2)
        // row = 0
        // col = 0
    
        d.location_x = row
        d.location_y = col
        }

        //  -- no requests -- adjust this logic later to avoid unsat with wellformed and init running together
        // no d.current_request --INITIALLY
        // no d.next_request --INITIALLY
        // no d.accepted_requests

        --passenger logic
        p.request.fulfilled = 0
        p.request.claimed = 0

        p.request.origin_x = d.location_x implies{
            p.request.origin_y != d.location_y
        }

        -- no passengers in cars to begin with
        p not in d.passengers_in_car

        -- passenger begins at requested location
        Board.pos_pass[p.request.origin_x][p.request.origin_y] = p
    }
        -- people relatively spread on board --> not sure how to do this yet
}

//wellformed: (hold true for all states)
-- specify the board/grid/map
-- fill in the middle squares that cannot nothing will be on --> to make an 8
-- Car
-- requests
-- passengers, drivers
-- movement abilities
-- capactiy between 0 and 5 (5 just chosen arbitrarily)

pred wellformed{


    --ALSO handle bounds of driver and passenger requets

        --requets all tied to a passenger
        all r: Request {
            some p: Passenger, d: Driver | {
                p.request = r
                (d.current_request = r) or
                (d.next_request = r) or
                (d.accepted_requests) = r
            }
        }

        all d: Driver | {
            -- can probably do this in a better way
            
            // d.current_request.origin_x >=0 and d.current_request.origin_x <=4
            // d.current_request.origin_y >=0 and d.current_request.origin_y <=2
            // d.current_request.destination_x >=0 and d.current_request.destination_x <=2
            // d.current_request.destination_y >=0 and d.current_request.destination_y <=2

            // d.next_request.origin_x >=0 and d.next_request.origin_x <=4
            // d.next_request.origin_y >=0 and d.next_request.origin_y <=2
            // d.next_request.destination_x >=0 and d.next_request.destination_x <=2
            // d.next_request.destination_y >=0 and d.next_request.destination_y <=2

            // d.current_request.fulfilled = 0 or d.current_request.fulfilled = 1
            // d.current_request.claimed = 0 or d.current_request.claimed = 1
            
            // d.next_request.fulfilled = 0 or d.next_request.fulfilled = 1
            // d.next_request.claimed = 0 or d.next_request.claimed = 1

            //d.current_request.party_size >= 0 or d.current_request.party_size <= 4
            // d.next_request.party_size = 0 or d.next_request.party_size <= 4

            one r, c: Int | {
                (r >= 0) and (r <= 4)
                (c >= 0) and (c <= 2)

                // d in (Board.position[r][c]).drivers //parens are a must --specify d in board.position

                d.location_x = r
                d.location_y = c

                d.capacity <= 4 //exclude driver in capacity to avoid math
                d.capacity >= 0

                 -- ensure not more passengers than capacity
                 #{d.passengers_in_car} <= d.capacity //might not need this later     
        }
    }

        -- people relatively spread on board

        --passenger should stay still unless picked up by driver!

        all p: Passenger | {
            one p.request
            p.request.party_size >= 0
            p.request.party_size <= 4 //later change this to current capacity

            p.request.origin_x >= 0
            p.request.origin_y >= 0
            p.request.origin_x <= 4
            p.request.origin_y <= 2
            p.request.destination_x >= 0
            p.request.destination_y >= 0
            p.request.destination_x <= 4
            p.request.destination_y <= 2

            (p.request.fulfilled = 0) or (p.request.fulfilled = 1)
            (p.request.claimed = 0) or (p.request.claimed = 1)

            (p.request.origin_x = p.request.destination_x) implies{
                p.request.origin_y != p.request.destination_y
            }
            some d : Driver | p not in d.passengers_in_car implies{
                Board.pos_pass[p.request.origin_x][p.request.origin_y] = p
            }
        }
}

// run {
//     wellformed_map
//     init
//     wellformed
// } for exactly 1 Driver, 1 Passenger

--Today: move predicates!!

pred moveRightEnabled[d: Driver]{
    d.location_x != 2 //can't move right if on edge
    (d.location_x != 0 and d.location_y != 1)
    (d.location_x != 0 and d.location_y != 3)
}

pred moveRight[d: Driver]{
    --column increases, row stays the same
    moveRightEnabled[d]

    -- next position needs to be row same, location_y + 1
    //(Board.pos_driver[d.location_x][d.location_y])' = (Board.pos_driver[d.location_x][add[d.location_y,1]])
    d.location_y' = d.location_y
    d.location_x' = add[d.location_x,1]
    (Board.pos_driver[d.location_x][d.location_y])' = d

    -- everything else stays the same
    d.capacity' = d.capacity
    d.accepted_requests' = d.accepted_requests
    d.current_request' = d.current_request
    d.next_request' = d.next_request
    d.passengers_in_car' = d.passengers_in_car

    -- 
    all p: d.passengers_in_car | {
        (Board.pos_pass[d.location_x][d.location_y])' = p
        // p.request.claimed' = 1
        //p.request.fulfilled' = p.request.fulfilled
    }
}

pred moveLeftEnabled[d: Driver]{
    d.location_x != 0 //can't move right if on edge
    (d.location_x != 2 and d.location_y != 1)
    (d.location_x != 2 and d.location_y != 3)
}


pred moveLeft[d: Driver]{
    --column increases, row stays the same
    moveLeftEnabled[d]

    -- next position needs to be row same, location_y + 1
    //(Board.pos_driver[d.location_x][d.location_y])' = 
    //(Board.pos_driver[d.location_x][subtract[d.location_y,1]])' = d
    d.location_y' = d.location_y
    d.location_x' = subtract[d.location_x,1]
    (Board.pos_driver[d.location_x][d.location_y])' = d

    -- everything else stays the same
    d.capacity' = d.capacity
    d.accepted_requests' = d.accepted_requests
    d.current_request' = d.current_request
    d.next_request' = d.next_request
    d.passengers_in_car' = d.passengers_in_car

    all p: d.passengers_in_car | {
       (Board.pos_pass[d.location_x][d.location_y])' = p
        // p.request.claimed' = 1
        //p.request.fulfilled' = p.request.fulfilled
    }
}

pred moveUpEnabled[d: Driver]{
    d.location_y != 0 //can't move right if on edge
    (d.location_x != 1 and d.location_y != 4)
    (d.location_x != 1 and d.location_y != 2)
}

pred moveUp[d: Driver]{
    --column increases, row stays the same
    moveUpEnabled[d]

    -- next position needs to be row same, location_y + 1
    //(Board.pos_driver[d.location_x][d.location_y])' = (Board.pos_driver[add[d.location_x, 1]][d.location_y])
    //(Board.pos_driver[add[d.location_x, 1]][d.location_y])' = d
    d.location_y' = add[d.location_y,1]
    d.location_x' = d.location_x
    (Board.pos_driver[d.location_x][d.location_y])' = d
    -- everything else stays the same
    d.capacity' = d.capacity
    d.accepted_requests' = d.accepted_requests
    d.current_request' = d.current_request
    d.next_request' = d.next_request
    d.passengers_in_car' = d.passengers_in_car
    all p: d.passengers_in_car | {
        (Board.pos_pass[d.location_x][d.location_y])' = p
        // p.request.claimed' = 1
        //p.request.fulfilled' = p.request.fulfilled
    }
}

pred moveDownEnabled[d: Driver]{
    d.location_y != 2 //can't move right if on edge
    (d.location_x != 1 and d.location_y != 0)
    (d.location_x != 1 and d.location_y != 2)
}

pred moveDown[d: Driver]{
    --column increases, row stays the same
    moveDownEnabled[d]

    -- next position needs to be row same, location_y + 1
  
    //(Board.pos_driver[d.location_x][d.location_y])' = (Board.pos_driver[subtract[d.location_x, 1]][d.location_y])
    //(Board.pos_driver[subtract[d.location_x, 1]][d.location_y])' = d
    d.location_y' = subtract[d.location_y, 1]
    d.location_x' = d.location_x
    (Board.pos_driver[d.location_x][d.location_y])' = d
    -- everything else stays the same
    d.capacity' = d.capacity
    d.accepted_requests' = d.accepted_requests
    d.current_request' = d.current_request
    d.next_request' = d.next_request
    d.passengers_in_car' = d.passengers_in_car
    all p: d.passengers_in_car | {
        (Board.pos_pass[d.location_x][d.location_y])' = p
        // p.request.claimed' = 1
        //p.request.fulfilled' = p.request.fulfilled
    }
}

pred stayStill[d: Driver]{
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    --add all the other constraints later
    -- everything stays the same:
    d.capacity' = d.capacity
    d.accepted_requests' = d.accepted_requests
    d.current_request' = d.current_request
    d.next_request' = d.next_request
    d.passengers_in_car' = d.passengers_in_car
}

--today 
 --pick up logic
 --drop off logic
 --passenger moves with car
 --then start to work out kinks
// pred pickUpCurIfRequesting[d: Driver] {
// 	pickUpEnabled[e] => pickUp[e]
// }

pred pickUpEnabled[d: Driver, p: Passenger] {
     // if a driver is in the same cell as a passenger
    // and they are sharing a request of some sort (don't have have to worry about this for now)
    d.location_x = p.request.origin_x
    d.location_y = p.request.origin_y
    p.request.claimed = 0
    p.request.fulfilled = 0
    //capacity is greater than number of passengers in car + party size
    d.capacity >= (add[#{d.passengers_in_car}, p.request.party_size])
}

pred pickUp[d: Driver, p: Passenger] {
    pickUpEnabled[d,p]

    // driver location stays still during pick up 
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    // passenger added to driver' passengers
    p in d.passengers_in_car'

    // request doesn't rly change
    p.request.claimed' = 1
    p.request.fulfilled' = p.request.fulfilled

    p.request in d.accepted_requests'
    d.current_request' = p.request
    d.next_request' = d.next_request
    
    (Board.pos_pass[p.request.origin_x][p.request.origin_y])' = p
}

//maybe doesnt need passenger
pred dropOffEnabled[d: Driver, p: Passenger] {
    d.location_x = p.request.destination_x
    d.location_y = p.request.destination_y

    //do we need to say that a passenger is in a car??
    p in d.passengers_in_car
}

pred dropOff[d: Driver, p: Passenger] {
    dropOffEnabled[d,p]
    //location stays the same:
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    p.request.fulfilled' = 1
    p.request.claimed' = 0 //goes back to being unclaimed?? how do we want to handle this

    //passenger no longer in driver' passengers
    p not in d.passengers_in_car'

    //removed from accepted requests (if thats how we choose to handle it)
    p.request not in d.accepted_requests'
    // d.current_request' = p.request -- not sure how to handle this
    // d.next_request' = d.next_request
    (Board.pos_pass[p.request.destination_x][p.request.destination_y])' = p
}

//actions:
-- for every passenger if there request is being fulfilled they are in a car
-- passengers need to move with the car
-- when a car picks up a passenger, the passenger moves with the car

--move in a direction (up, down, left, right)
-- pick up a person (at location)
-- drop someone off (at location)
-- enabled
-- stay still/do nothing --> passenger does not move without a car
-- if there is a request driver should be moving towards it in its next state

--accepting request
 --p.request.party_size <= (d.car.capacity - #{d.car.passengers_in_car}) --> move to accepting request logic


//traces: 
--reasonable pick up and drop off logic

//procedures

//Tests!!!!!!!!!!!!!!!!

// 0 0 0
// 0 X 0
// 0 0 0
// 0 X 0
// 0 0 0

//last but not least..... visualizer

pred traces {
    always wellformed_map
    always wellformed
    init --maybe
    // all d: Driver | moveRight[d]//always{moveRight[d] or stayStill[d]}
    all d: Driver, p: Passenger | always{
        moveRight[d] or moveLeft[d] or moveUp[d] or moveDown[d] or pickUp[d,p] or dropOff[d,p]
        eventually{pickUp[d,p]}
        // eventually {{not dropOff[d,p]} until{{pickUp[d,p]}}}
        // always {eventually {dropOff[d, p]}}
        // eventually{pickUp[d,p]} implies {dropOff[d,p]}
        --cant seem to get pickup and drop off to work together
        -- I want to say that we always eventually pick up and then because we pick up
            --we always eventually drop off
        // not dropOff[d,p] until{pickUp[d,p]}
        // eventually{pickUp[d,p]}
        // eventually{dropOff[d,p]}

    }
    
}

run{
    traces
} for exactly 1 Driver, 1 Passenger
