abstract sig Status {}
one sig On, Off extends Status {}

abstract sig Counter {}
one sig  C0, C1 extends Counter {}

abstract sig Op {}
one sig rOn, yOn, gOn, noOp extends Op {}

one sig TrafficLight {
  var red: Status, 
  var yellow: Status,  
  var green: Status,
  var count: Counter,
  var op: Op
}
fun R : Status { TrafficLight.red }
fun Y : Status { TrafficLight.yellow }
fun G : Status { TrafficLight.green }
fun c : Counter { TrafficLight.count }
fun o : Op { TrafficLight.op }

pred redOn {
  -- preconditions
  c = C0
  Y = On
  -- postconditions
  R' = On
  Y' = Off
  c' = C1
  -- frame conditions
  G' = G

  o' = rOn
}

pred greenOn {
  -- preconditions
  c = C0
  R = On
  -- postconditions
  R' = Off
  G' = On
  c' = C1
  -- frame conditions
  Y' = Y

  o' = gOn
}

pred yellowOn {
  -- preconditions
  c = C0
  G = On
  -- postconditions
  G' = Off
  Y' = On
  -- frame conditions
  R' = R
  c' = c

  o' = yOn
}

pred steady {
  -- preconditions
  c != C0
  -- postconditions
  c' = C0  
  -- frame conditions
  R' = R
  G' = G
  Y' = Y
  o' = noOp
}

fact {
  -- Initial state condition
  R = On
  G = Off
  Y = Off 
  c = C1
  o = noOp
  -- transition predicate
  always (redOn or greenOn or yellowOn or steady)
}

run system {}

-- each light repeatedly turns on
-- no two lights are on at the same time
-- one of the lights is on any one time
-- the light starts with red only
-- green directly follows red

-- yellow directly follows green
-- red and green are on exactly twice in a row
-- yellow is never on twice in a row
-- red does not follow green





assert each_light_repeatedly_turns_on {
  always eventually (R = Off and after R = On)
  always eventually (G = Off and after G = On)
  always eventually (Y = Off and after Y = On)
}
check each_light_repeatedly_turns_on for 20 steps

assert no_two_lights_are_on_at_the_same_time {
  always (R = On => G = Off and Y = Off)
  always (G = On => R = Off and Y = Off)
  always (Y = On => R = Off and G = Off)
}
check no_two_lights_are_on_at_the_same_time for 20 steps

assert one_of_the_lights_is_on_any_one_time {
  always (R = On or Y = On or G = On)
--  always not (R = Off and Y = Off and G = Off)
}
check one_of_the_lights_is_on_any_one_time for 20 steps

assert the_light_starts_with_red_only {
  R = On
  G = Off
  Y = Off
}
check the_light_starts_with_red_only for 20 steps

assert green_directly_follows_red {
  always (G = Off and after G = On implies R = On)
}
check green_directly_follows_red for 20 steps

assert yellow_is_neverOn_twice_in_a_row {
  always (Y = On implies after Y = Off)
}
check yellow_is_neverOn_twice_in_a_row for 20 steps

assert red_is_always_on_twice_in_a_row {
  -- at least twice 
  always (R = Off and after R = On implies
          after after R = On)  
  -- at most twice
  always (before R = On and R = On implies
          after R = Off)   
}
check red_is_always_on_twice_in_a_row

assert red_does_not_follow_green {
  always (after R = On implies G = Off)
}
check red_does_not_follow_green for 20 steps
