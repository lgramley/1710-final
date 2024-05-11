#lang forge/temporal
option run_sterling "vis.js"

option max_tracelength 25
option min_tracelength 6
// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

--Sigs--
sig Request {
    party_size: one Int,
    var fulfilled: one Int, //(0 , 1)
    var claimed: one Int, //(0 , 1)
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

//init: (initial state)
pred init{

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
pred wellformed{
        --requets all tied to a passenger
        all r: Request {
            some p: Passenger | {
                p.request = r
            }
            r.party_size > 0
            r.party_size <= 4 

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
            d.capacity <= 4 //exclude driver in capacity to avoid math
            d.capacity >= 0

            -- ensure not more passengers than capacity
        }


        --no drivers cannot accept the same requests
        all disj d1, d2: Driver | {
            (d1.accepted_requests not in d2.accepted_requests and d2.accepted_requests not in d1.accepted_requests) or no d1.accepted_requests or no d2.accepted_requests
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

            all p2:Passenger | p != p2 =>{
                p.request != p2.request

            }      
        }
}

pred requestsStaySame {
    all r: Request | {
        r.fulfilled' = r.fulfilled
        r.claimed' = r.claimed
    }
}

pred moveRightEnabled[d: Driver]{
    not {d.location_x >= 4 //can't move right if on edge
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
    not{d.location_x <= 0 //can't move left if on edge
    or (d.location_x = 2 and d.location_y = 1)
    or (d.location_x = 4 and d.location_y = 1)}
}


pred moveLeft[d: Driver]{
    --column decreases, row stays the same
    moveLeftEnabled[d]

    -- next position needs to be row same, location_y - 1
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

    not{d.location_y >= 2 //can't move up if on edge
    or (d.location_x = 1 and d.location_y = 0)
    or (d.location_x = 3 and d.location_y = 0)}
}

pred moveUp[d: Driver]{
    --row increases, row stays the same
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
    not{d.location_y <= 0 //can't move right if on edge
    or (d.location_x = 1 and d.location_y = 2)
    or (d.location_x = 3 and d.location_y = 2)}
}

pred moveDown[d: Driver]{
    --column increases, row stays the same
    moveDownEnabled[d]

    -- next position needs to be row same, location_y - 1
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
    -- everything stays the same:
    d.accepted_requests' = d.accepted_requests
    d.passengers_in_car' = d.passengers_in_car
    
    requestsStaySame
    all p: Passenger |{
        p.locationx' = p.locationx
        p.locationy' = p.locationy
    }
}

pred claimingEnabled[d:Driver, p: Passenger]{
    //conditions in which it is acceptable to accept a request
    p.request.claimed = 0
    p.request.fulfilled = 0
    d.capacity >= (add[#{d.passengers_in_car}, p.request.party_size])
    p.request not in d.accepted_requests
}

pred claiming[d: Driver, p: Passenger]{
    claimingEnabled[d, p]

    p.request.claimed' = 1
    p.request.fulfilled' = p.request.fulfilled

    p.request in d.accepted_requests'

    -- driver should stay the same
    d.location_x' = d.location_x
    d.location_y' = d.location_y
    d.passengers_in_car' = d.passengers_in_car
    
}

pred pickUpEnabled[d: Driver, p: Passenger] {
    d.location_x = p.request.origin_x
    d.location_y = p.request.origin_y
    
    p.request in d.accepted_requests
    p.request.claimed = 1
}

pred pickUp[d: Driver, p: Passenger] {
    pickUpEnabled[d,p]

    // driver location stays still during pick up 
    requestsStaySame
    d.location_x' = d.location_x
    d.location_y' = d.location_y

    p.locationx' = p.locationx
    p.locationy' = p.locationy
    // passenger added to driver' passengers
    
    p in d.passengers_in_car'

    d.accepted_requests' = d.accepted_requests
    
}

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

    p.request.claimed' = p.request.claimed 

    //passenger no longer in driver' passengers
    d.passengers_in_car' = d.passengers_in_car - p
    d.accepted_requests' = d.accepted_requests - p.request
}


//traces: 
--reasonable pick up and drop off logic
pred acceptIfRequesting[d: Driver, p: Passenger]{
    claimingEnabled[d,p] => claiming[d,p]
}
pred pickUpCurIfRequesting[d: Driver, p: Passenger] {
	pickUpEnabled[d,p] => pickUp[d,p]
}

pred dropOffCurIfRequesting[d: Driver, p: Passenger] {
    dropOffEnabled[d,p] => dropOff[d,p]
}


pred traces {
    always wellformed
    init 
    all d: Driver| some p: Passenger | {
        always {moveRight[d] or moveLeft[d] or moveUp[d] or moveDown[d] or claiming[d,p] or stayStill[d] or pickUp[d,p] or dropOff[d,p]}
        eventually{dropOff[d,p]}
        always dropOffCurIfRequesting[d,p]    
    } 
}


run{
    traces
} for exactly 2 Driver, exactly 2 Passenger


--left right enforcers
--this procedure enforces that the driver moves left until it cannot move left anymore or
    --right until it cannot anymore/hits the boundary
pred procedure1[d: Driver, p: Passenger]{
    no p.request iff stayStill[d]
    
    d.location_x > p.request.origin_x => moveLeft[d]
    d.location_x < p.request.origin_x => moveRight[d]
}

--up down enforcers
--this procedure enforces that the driver moves up until it cannot move up anymore or
    --right down it cannot anymore/hits the boundary
pred procedure2[d: Driver, p: Passenger]{
    no p.request iff stayStill[d]

    d.location_y > p.request.origin_y => moveDown[d]
    d.location_y < p.request.origin_y => moveUp[d]
}

//no turnaround
--this procedure enforces that a car never turns around until it hits a boarder
pred procedure3[d: Driver, p: Passenger]{
    no p.request iff stayStill[d]

    d.location_x' = add[d.location_x, 1] => moveRight[d] until d.location_x = 4
    d.location_x' = subtract[d.location_y, 1] => moveLeft[d] until d.location_x = 0
    d.location_y' = add[d.location_y, 1] => moveUp[d] until d.location_y = 2
    d.location_y' = subtract[d.location_y, 1] => moveDown[d] until d.location_y = 0
}

//does not claim unless at same block
--this procedure enforces that a driver does not claim a passenger unless it is within a block of that passenger
pred procedure4[d: Driver, p:Passenger]{
    no p.request iff stayStill[d]
    {(subtract[d.location_x, p.locationx] = 1 or subtract[p.locationx, d.location_x] = 1) and (subtract[d.location_y, p.locationy] = 1 or subtract[p.locationy, d.location_y] = 1)} => claiming[d,p]
}

//does not claim unless at passenger
--this procedure enforces that a driver does not claim a passenger until it is on the same spot as the passenger 
pred procedure5[d: Driver, p:Passenger]{
    no p.request iff stayStill[d]
    claimingEnabled[d,p] iff {subtract[d.location_x, p.locationx] = 0 or subtract[p.locationx, d.location_x] = 0 or subtract[d.location_y, p.locationy] = 0 or subtract[p.locationy, d.location_y] = 0}
}

--board layout
--drivers and passengers cannot be at blocked off locations

--0 0 0 0 0--
--0 X 0 X 0--
--0 0 0 0 0--

