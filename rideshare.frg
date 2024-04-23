#lang forge/temporal
option max_tracelength 14


--Sigs--
sig Request {
    party_size: one Int,
    var fulfilled: one Int, //(0 or 1)
    origin: one Int,
    destination: one Int
}

sig Passenger {
    request: one Request
}

sig Car{
    capacity: one Int,
    var current_passengers: Int,
    var Location: Int
}

-- I think this is the main sig
sig Driver {
    var accepted_requests: set Request,
    car: Car,
    var next_request: one Request
}

abstract sig Direction {}
one sig East extends Direction {} --just fowards and backwards for now
one sig West extends Direction {}

--RequestList (global list of requests)
sig RequestsList{
    var all_requests: set Request
}



