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

sig Car{
    capacity: one Int,
    var location_x: lone Int,
    var location_y: lone Int,
    passengers_in_car: set Passenger
}

sig Driver {
    car: one Car,
    var accepted_requests: set Request,
    var current_request: one Request,
    var next_request: one Request
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

sig Tile{
    passengers: set Passenger,
    drivers: set Driver
}

one sig Board {
    var position : pfunc Int -> Int -> Tile // (int, int) -> thing
}

pred wellformed_map {
  // Fill in this predicate to ensure that:
  // Each tile is positioned on exactly one square
  // The board is 5x3, so Int ranges from 0-4 and 0-2
  all t: Tile | {
    one r, c: Int | {
    (r >= 0) and (r <= 4)
    (c >= 0) and (c <= 2)
    Board.position[r][c] = t
    }
  }

  no t: Tile | {
    some r, c : Int {
    (r < 0) or (r > 4) or (c < 0) or (c > 2)
    (r = 1) and (c = 1) //fill in upper middle square
    (r = 3) and (c = 1) //fill in lower middle square
    Board.position[r][c] = t
    }
  }
} 

//Todo:
-- GOAL: car moves in a direction (ideally towards a passenger)
-- start with one car and passenger and then build up to a whole network of cars and passengers

//init: (initial state)
-- Passengers and Cars relatively spread out across the board
pred init{
    -- cars at origin 
    all t: Tile | {
        all d: Driver | {
            d in t.drivers
            one r, c: Int | {
            (r >= 0) and (r <= 4)
            (c >= 0) and (c <= 2)
        
            d.car.location_x = r
            d.car.location_y = c
        }
    }

        -- people relatively spread on board

        all p: Passenger | {
            p in t.passengers
            p.request.fulfilled = 0
            p.request.claimed = 0

            one x, y: Int | {
                (x >= 0) and (x <= 4) and (y >= 0) and (y <= 2)
                p.request.origin_x = x
                p.request.origin_y = y
            }
        }
    }

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
    all t: Tile | {
        all d: Driver | {
            d in t.drivers
            one r, c: Int | {
            (r >= 0) and (r <= 4)
            (c >= 0) and (c <= 2)
            
            d.car.location_x = r
            d.car.location_y = c

            d.car.capacity <= 5
            d.car.capacity >= 0

            some p: Passenger | {
                no p or
                p in d.car.passengers_in_car
            }
        }
    }

        -- people relatively spread on board

        all p: Passenger | {
            p in t.passengers

            p.request.party_size >=0
            p.request.party_size <= 5 //later change this to current capacity

            one x, y, xx, yy: Int | {
                (xx = x) implies {y != yy} //origin does not equal destination

                (x >= 0) and (x <= 4) and (y >= 0) and (y <= 2)
                (xx >= 0) and (xx <= 4) and (yy >= 0) and (yy <= 2)
                
                p.request.origin_x = x
                p.request.origin_y = y

                p.request.destination_x = xx
                p.request.destination_x = yy

            }
        }
    }

}

run {
    wellformed_map
    init
    wellformed
} for exactly 1 Driver, 1 Passenger

//actions:
-- passengers need to move with the car
-- when a car picks up a passenger, the passenger moves with the car

--move in a direction (up, down, left, right)
-- pick up a person (at location)
-- drop someone off (at location)
-- enabled
-- stay still/do nothing

--accepting request

//traces: 
--reasonable pick up and drop off logic

//procedures:

// 0 0 0
// 0 X 0
// 0 0 0
// 0 X 0
// 0 0 0

//last but not least..... visualizer

