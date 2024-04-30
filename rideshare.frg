#lang forge/temporal
option max_tracelength 14


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

// sig Car{
//     capacity: one Int,
//     // var location_x: lone Int,
//     // var location_y: lone Int,
//     passengers_in_car: set Passenger
// }

sig Driver {
    capacity: one Int,
    var accepted_requests: set Request,
    var current_request: one Request,
    var next_request: one Request,
    var location_x: lone Int,
    var location_y: lone Int,
    passengers_in_car: set Passenger
}

abstract sig Direction {}
one sig East extends Direction {} 
one sig West extends Direction {}
one sig North extends Direction {}
one sig South extends Direction {}

--RequestList (global list of requests)
sig RequestsList{
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
    
        d.location_x = row
        d.location_y = col
        }

         -- no requests
        no d.current_request --INITIALLY
        no d.next_request --INITIALLY
        no d.accepted_requests

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

        all d: Driver | {
            -- can probably do this in a better way
            d.current_request.origin_x >=0 and d.current_request.origin_x <=4
            d.current_request.origin_y >=0 and d.current_request.origin_y <=2
            d.current_request.destination_x >=0 and d.current_request.destination_x <=2
            d.current_request.destination_y >=0 and d.current_request.destination_y <=2

            d.next_request.origin_x >=0 and d.next_request.origin_x <=4
            d.next_request.origin_y >=0 and d.next_request.origin_y <=2
            d.next_request.destination_x >=0 and d.next_request.destination_x <=2
            d.next_request.destination_y >=0 and d.next_request.destination_y <=2

            d.current_request.fulfilled = 0 or d.current_request.fulfilled = 1
            d.current_request.claimed = 0 or d.current_request.claimed = 1
            d.next_request.fulfilled = 0 or d.next_request.fulfilled = 1
            d.next_request.claimed = 0 or d.next_request.claimed = 1

            d.current_request.party_size >= 0 or d.current_request.party_size <= 4
            d.next_request.party_size = 0 or d.next_request.party_size <= 4



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

        all p: Passenger | {

            p.request.party_size >= 0
            p.request.party_size <= 4 //later change this to current capacity



            one x, y, xx, yy: Int | {
                not ((xx = x) and {y = yy}) //origin does not equal destination

                (x >= 0) and (x <= 4) and (y >= 0) and (y <= 2)
                (xx >= 0) and (xx <= 4) and (yy >= 0) and (yy <= 2)
                
                (p.request).origin_x = x
                (p.request).origin_y = y

                (p.request).destination_x = xx
                (p.request).destination_x = yy
            }
        }
}

run {
    wellformed_map
    // init
    wellformed
} for exactly 1 Passenger, 1 Driver

--Today: move predicates!!

// pred moveEastEnabled[d: Driver]{
//     d.location_x != 2 //can't move right if on edge

//     some p: Passenger | {
//         p.request = 
//     }
// }

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

//procedures:

// 0 0 0
// 0 X 0
// 0 0 0
// 0 X 0
// 0 0 0

//last but not least..... visualizer

