abstract sig Color {}

one sig Green, Yellow, Red extends Color {}

one sig TrafficLight {
  var col: Color
}

fun c: Color { TrafficLight.col }

pred g { TrafficLight.col = Green }
pred y { TrafficLight.col = Yellow }
pred r { TrafficLight.col = Red }

-- p 				<=>  p holds in the current state
-- eventually p		<=>  p holds in the current state or a later one
-- always p			<=>  p holds from current state forward
-- after p			<=>  p holds in the next state
-- p until q		<=>  q holds eventually and  
--                       p holds continuously until then
-- once p			<=>  p holds in current state or an earlier one
-- historically p	<=>  p holds from current state backward
-- before p			<=>  p holds in the previous state 
-- p since q		<=>  p has held continuously since last time q held 
-- e’				 =   the value of e in next state

pred demo {
  g
  after y
  after after r
  after after after r
  after after after after g
}

run demo


assert a1 { demo implies
 g
-- r
-- eventually r
-- eventually (r and after r)
-- always (g implies after y)
-- eventually (y and after g)
-- eventually (r implies once g)
-- always (not g implies r)
-- always (not g implies (y or r))
}
check a1 for 20 steps



pred TL_protocol {

-- 0. each light repeatedly turns on


-- 1. the light starts with red
r

-- 2. green directly follows red

-- 3. yellow directly follows green

-- 4. red does not follow green

-- 5. red is on at least twice in a row


-- 6. red is on at most twice in a row

-- 7. green is on at least twice in a row

-- 8. yellow is on at most once at a time

}

run TL_protocol
 
assert a2 { 
-- no two lights are on at the same time
    not (r and g) 
and not (r and y)  
and not (g and y)  
}
check a2 for 20 steps

assert a3 { TL_protocol implies
r
--  eventually y
--  not eventually (before y and y)
--  always (r implies eventually g)
--  always (y implies before g)
--  always (y implies after not y)
--  r until g
--  always (g implies g until y) 
--  always (g implies g since r)
--  eventually (before g and g and after g)

}
check a3 for 18 steps


