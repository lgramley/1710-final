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

pred Wellformed_map {
  // Fill in this predicate to ensure that:
  // Each tile is positioned on exactly one square
  // The board is 5x3, so Int ranges from 0-4 and 0-2
  all t: Tile | {
    one r, c: Int | {
    r >= 0
    r <= 4
    c >= 0
    c <= 2
      Board.position[r][c] = t
    }
  }

  no t: Tile | {
    some r, c : Int {
    (r < 0) or (r > 4) or (c < 0) or (c > 2)
    Board.position[r][c] = t
    }
  }
} 

run {
    Wellformed_map
}

//Todo:
-- GOAL: car moves in a direction (ideally towards a passenger)
-- start with one car and passenger and then build up to a whole network of cars and passengers

//init: (initial state)
-- Passengers and Cars relatively spread out across the board

//wellformed: (hold true for all states)
-- specify the board/grid/map
-- fill in the middle squares that cannot nothing will be on --> to make an 8
-- Car
-- requests
-- passengers, drivers
-- movement abilities

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

