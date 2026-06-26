---------------- Signatures ----------------

abstract sig Person {
	children: set Person,
	siblings: set Person
} 

sig Man, Woman extends Person {}

sig Married in Person {
	spouse: one Married 
}
---------------- Functions ----------------

-- Define the parents relation as an auxiliary one
fun parents [] : Person -> Person { ~children }

---------------- Predicate ----------------

-- Two persons are blood relatives iff they have a common ancestor
pred BloodRelatives [p: Person, q: Person] {
	some p.*parents & q.*parents
}

---------------- Facts ----------------

fact {

	-- No person can be their own ancestor
	no p: Person | p in p.^parents

	-- Nobody can have more than one father or mother
	all p: Person | (lone (p.parents & Man)) and (lone (p.parents & Woman)) 

	-- Your siblings are those people other than you who have the same parent as you
	all p: Person | p.siblings = {q: Person | p.parents = q.parents} - p

	-- Each married man (woman) has a wife (husband) 
	all p: Married | let s = p.spouse |
		(p in Man implies s in Woman) and
		(p in Woman implies s in Man)

	-- A spouse can't be a siblings
	no p: Married | p.spouse in p.siblings

	-- A person can't be married to a blood relative
	no p: Married | BloodRelatives [p, p.spouse]

	-- A person can't have children with a blood relative
	all p, q: Person |
		(some p.children & q.children and p != q) implies
        not BloodRelatives [p, q]
}


------------------- Run ---------------------
-- with a scope 1 and include a married man
run scenario1 {some Man & Married} for 1		-- (not satisfiable)

-- with a scope 2 and include a married man
run scenario2 {some Man & Married} for 2		

-- with a scope 3 and include a married man
run scenario3 {some Man & Married}			

-- include a woman but no men
run scenario4 {#Woman >= 1 and #Man = 0}			

-- not satisfiable
run scenario5 {some Man and some Married and no Woman}	

run scenario6 {some p: Person | some p.children}


---------------- Assertions ----------------

-- No person has a parents that's also a siblings.
assert parentsArentSiblings {    
	all p: Person | no p.parents & p.siblings 
}
check parentsArentSiblings for 10

-- Your siblings are the same as your siblings' siblings. 
assert siblingsSiblings {
	all p: Person | p.siblings = p.siblings.siblings
}
check siblingsSiblings

-- No person shares a common ancestor with his spouse 
-- (i.e., spouse isn't related by blood). 
assert NoIncest {
	no p: Married | 
		some (p.^parents & p.spouse.^parents)
}
check NoIncest




