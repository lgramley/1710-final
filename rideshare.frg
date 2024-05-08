#lang forge/temporal
option max_tracelength 25
//option min_tracelength 10
option solver MiniSatProver
option core_minimization rce
option logtranslation 1
option coregranularity 1

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
    request: one Request,
    var locationx: one Int,
    var locationy: one Int
}

sig Driver {
    capacity: one Int,
    var accepted_requests: set Request,
    var location_x: one Int,
    var location_y: one Int,
    var passengers_in_car: set Passenger
}

--RequestList (global list of requests)
one sig RequestsList{
    var all_requests: set Request
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
        --passenger logic
        p.request.fulfilled = 0
        p.request.claimed = 0

        p.request.origin_x = d.location_x implies{
            p.request.origin_y != d.location_y
        }

        -- no passengers in cars to begin with
        p not in d.passengers_in_car

        p.request not in d.accepted_requests
        -- passenger begins at requested location
        p.locationx = p.request.origin_x
        p.locationy = p.request.origin_y
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
            }
            r.party_size >= 0
            r.party_size <= 4 //later change this to current capacity

            r.origin_x >= 0
            r.origin_y >= 0
            r.origin_x <= 4
            r.origin_y <= 2
            r.destination_x >= 0
            r.destination_y >= 0
            r.destination_x <= 4
            r.destination_y <= 2

            (r.fulfilled = 0) or (r.fulfilled = 1)
            (r.claimed = 0) or (r.claimed = 1)

            (r.origin_x = r.destination_x) implies{
                r.origin_y != r.destination_y
            }
            r in RequestsList.all_requests
        }

        all d: Driver | {
            -- can probably do this in a better way
            d.capacity <= 4 //exclude driver in capacity to avoid math
            d.capacity >= 0

            -- ensure not more passengers than capacity
        }

        all disj d1, d2: Driver |{
            d1.accepted_requests not in d2.accepted_requests
            d2.accepted_requests not in d1.accepted_requests
        }

        --passenger should stay still unless picked up by driver!
        all p: Passenger | {
            
            // if they are not in a car, they cannot move
            some d: Driver | p not in d.passengers_in_car implies {
                some x, y: Int | {
                    p.locationx' = p.locationx
                    p.locationy' = p.locationy
                }
            }         
        }
}


--Today: move predicates!!
pred requestsStaySame {
    all r: Request | {
        r.fulfilled' = r.fulfilled
        r.claimed' = r.claimed
    }
}

pred moveRightEnabled[d: Driver]{
    not {d.location_x = 4 //can't move right if on edge
    or (d.location_x = 0 and d.location_y = 1)
    or (d.location_x = 2 and d.location_y = 1)}
}

pred moveRight[d: Driver]{
    --column increases, row stays the same
    moveRightEnabled[d]

    -- next position needs to be row same, location_y + 1
    d.location_y' = d.location_y
    d.location_x' = add[d.location_x,1]
 

    -- everything else stays the same
   
    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car
    -- 
    all p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' = add[p.locationx,1]
    
    }
    requestsStaySame
}

pred moveLeftEnabled[d: Driver]{
    not{d.location_x = 0 //can't move right if on edge
    or (d.location_x = 2 and d.location_y = 1)
    or (d.location_x = 4 and d.location_y = 1)}
}


pred moveLeft[d: Driver]{
    --column increases, row stays the same
    moveLeftEnabled[d]

    -- next position needs to be row same, location_y + 1
    d.location_y' = d.location_y
    d.location_x' = subtract[d.location_x,1]
    

    -- everything else stays the same

    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car

    all p: d.passengers_in_car | {
        p.locationy' = p.locationy
        p.locationx' = subtract[p.locationx,1]
    }
    requestsStaySame
}

pred moveUpEnabled[d: Driver]{
    not{d.location_y = 2 //can't move up if on edge
    or (d.location_x = 1 and d.location_y != 0)
    or (d.location_x = 3 and d.location_y = 0)}
}

pred moveUp[d: Driver]{
    --column increases, row stays the same
    moveUpEnabled[d]

    -- next position needs to be row same, location_y + 1
    d.location_y' = add[d.location_y,1]
    d.location_x' = d.location_x
    -- everything else stays the same
    
    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car
    all p: d.passengers_in_car | {
        p.locationy' = add[p.locationy,1]
        p.locationx' = p.locationx
    }

    requestsStaySame
}

pred moveDownEnabled[d: Driver]{
    not{d.location_y = 0 //can't move right if on edge
    or (d.location_x = 1 and d.location_y = 2)
    or (d.location_x = 3 and d.location_y = 2)}
}

pred moveDown[d: Driver]{
    --column increases, row stays the same
    moveDownEnabled[d]

    -- next position needs to be row same, location_y + 1
    d.location_y' = subtract[d.location_y, 1]
    d.location_x' = d.location_x
   
    -- everything else stays the same
    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car
    all p: d.passengers_in_car | {
        p.locationy' = subtract[p.locationy, 1]
        p.locationx' = p.locationx
    }

    requestsStaySame
}

pred stayStill[d: Driver]{
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    --add all the other constraints later
    -- everything stays the same:
    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car
    
    requestsStaySame
    all p: Passenger |{
        p.locationx' = p.locationx
        p.locationy' = p.locationy
    }
}

pred pickUpEnabled[d: Driver, p: Passenger] {
     // if a driver is in the same cell as a passenger
    // and they are sharing a request of some sort (don't have have to worry about this for now)
    d.location_x = p.request.origin_x
    d.location_y = p.request.origin_y
    p.request.claimed = 0
    p.request.fulfilled = 0
    //capacity is greater than number of passengers in car + party size
    d.capacity >= (add[#{d.passengers_in_car}, p.request.party_size])
    p.request not in d.accepted_requests
}

pred pickUp[d: Driver, p: Passenger] {
    pickUpEnabled[d,p]

    // driver location stays still during pick up 
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    p.locationx' = p.locationx
    p.locationy' = p.locationy
    // passenger added to driver' passengers
    p in d.passengers_in_car'

    // request doesn't rly change
    p.request.claimed' = 1
    p.request.fulfilled' = p.request.fulfilled

    p.request in d.accepted_requests'
    
    
}

//maybe doesnt need passenger
pred dropOffEnabled[d: Driver, p: Passenger] {
    d.location_x = p.request.destination_x
    d.location_y = p.request.destination_y
    p in d.passengers_in_car
}

pred dropOff[d: Driver, p: Passenger] {
    dropOffEnabled[d,p]


    //location stays the same:
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    p.locationx' = p.locationx
    p.locationy' = p.locationy

    p.request.fulfilled' = 1
    // claimed goes back to 0 i guess

    p.request.claimed' = p.request.claimed //goes back to being unclaimed?? how do we want to handle this

    //passenger no longer in driver' passengers
    d.passengers_in_car' = d.passengers_in_car - p

    
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

pred pickUpCurIfRequesting[d: Driver, p: Passenger] {
	pickUpEnabled[d,p] => pickUp[d,p]
}

pred dropOffCurIfRequesting[d: Driver, p: Passenger] {
    dropOffEnabled[d,p] => dropOff[d,p]
}

pred traces {
    always wellformed
    init --maybe
    all d: Driver| some p: Passenger | {
        always {moveRight[d] or moveLeft[d] or moveUp[d] or moveDown[d] or pickUp[d,p] or dropOff[d,p] or stayStill[d]}
        eventually{pickUp[d,p]}
        eventually{dropOff[d,p]}
        always pickUpCurIfRequesting[d,p]
        always dropOffCurIfRequesting[d,p]
    }

    
}

run{
    traces
} for exactly 1 Driver, exactly 1 Passenger

// 0 0 0
// 0 X 0
// 0 0 0
// 0 X 0
// 0 0 0

//procedures
//Tests!
//write up
//visualizer?