open util/ordering [Key] as KO

sig Key {}

sig Room {
  keys: set Key,
  var currKey: Key
}

sig Guest {
  var keys: set Key
}

one sig FrontDesk {
  var lastKey: Room -> lone Key,
  var occupant: Room -> Guest
}

-- shorthands
fun FDlastKey: Room -> Key { FrontDesk.lastKey }
fun FDoccupant: Room -> Guest { FrontDesk.occupant }

enum Operator { Entry, CheckIn, CheckOut }

one sig Track {
  var op: lone Operator
}

fact {
  all k: Key | lone (Room <: keys).k
  always all r: Room | r.currKey in r.keys 
}

-----------------------
-- Auxiliary functions
-----------------------

fun nextKey [k: Key, ks: set Key]: set Key {
  KO/min [KO/nexts[k] & ks]
}

pred noFrontDeskChange {
  FDlastKey' = FDlastKey
  FDoccupant' = FDoccupant
}

pred noRoomChange [rs: set Room] {
  all r: rs | r.currKey' = r.currKey
}

pred noGuestChange [gs: set Guest] {
  all g: gs | g.keys' = g.keys
}

-------------
-- Operators
-------------

-- entry
pred entry [ g: Guest, r: Room, k: Key ] {
  -- preconditions
     -- the key used to open the lock is one of the keys held by the guest
     k in g.keys
  -- pre and post conditions
     (-- not a new guest
      k = r.currKey and r.currKey' = r.currKey 
      or 
      -- new guest
      k = nextKey[r.currKey, r.keys] and r.currKey' = k
     )
  -- frame conditions
     noFrontDeskChange
     noRoomChange[Room - r]
     noGuestChange[Guest]

  Track.op' = Entry
}

-- checkout
pred checkOut [g: Guest] {
  -- preconditions
     -- the guest occupies one or more rooms
     some FDoccupant.g

  -- postconditions
     -- the guest's room become available
     FDoccupant' = FDoccupant - (Room -> g)

  -- frame conditions
     FDlastKey' = FDlastKey
     noRoomChange[Room]
     noGuestChange[Guest]

  Track.op' = CheckOut
}

-- checkin
pred checkIn [ g: Guest, r: Room, k: Key ] {
  -- preconditions
     -- the room has no current occupant
     no r.FDoccupant
     -- the input key is the successor of the last key in 
     -- the sequence associated to the room
     k = nextKey[r.FDlastKey, r.keys]

  -- postconditions
     -- the guest becomes the new occupant of the room
     FDoccupant' = FDoccupant + (r -> g) 
     -- the guest holds the input key 
     g.keys' = g.keys + k
     -- the input key becomes the room's last key 
     FDlastKey' = FDlastKey ++ (r -> k)

  -- frame conditions
     noRoomChange[Room]
     noGuestChange[Guest - g]

  Track.op' = CheckIn
}

run test {}

---------------------------
-- Initial state predicate
---------------------------
pred init {
  -- no guests have keys
  no Guest.keys
  -- the roster at the front desk shows
  -- no room as occupied
  no FDoccupant
  -- the record of each room’s key at the
  -- front desk is synchronized with the
  -- current combination of the lock itself
  all r: Room | 
    r.FDlastKey = r.currKey

  no Track.op
}


fact Traces {
  init
  always some g: Guest, r: Room, k: Key |
       entry [g, r, k] 
    or checkIn [g, r, k]
    or checkOut [g] 
}


pred noInterveningOps {
  always all g: Guest, r: Room, k: Key |
    checkIn[g, r, k] implies after entry[g, r, k] 
}


assert noBadEntry  {
  noInterveningOps implies
    always all r: Room, g: Guest, k: Key | 
      let o = r.FDoccupant |
        (entry [g, r, k] and some o) implies g in o
}

check noBadEntry for 5
but 3 Room, 3 Guest, 20 steps
