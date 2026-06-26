/* Exercise

1. Complete the definition of the predicates restore and empty.
2. Using the Analyzer, show that the same file can be perpetually deleted.
3. Specify and verify the following properties stated for each empty
   assertion below.

Use only the following temporal operators:
always, after, once, and primes (').
*/

var sig File {}
var sig Trash in File {}

abstract sig Operator {}
one sig Delete, Restore, EmptyTrash, Other extends Operator {}

one sig Track { 
  var op: Operator
}

-- Delete a file
pred delete[f : File] { 
  f not in Trash
  Trash' = Trash + f 
  File' = File

  Track.op' = Delete
}

-- Restore a file
pred restore[f : File] {
  f in Trash
  Trash' = Trash - f 
  File' = File  

  Track.op' = Restore
} 


-- Empty the trash
pred emptyTrash {
  some Trash
  File' = File - Trash
  Trash' = none

  Track.op' = EmptyTrash
}

-- Do nothing
pred other {
  Trash' = Trash
  File' = File 

  Track.op' = Other
}


run Scenario1 {
  #File > 1
  eventually some f: File | delete[f]
  eventually some f: File | restore[f]
  eventually no File
}

--------------------------
-- File Management System
--------------------------

fact behavior { 
  -- initial state
  some File
  no Trash

  Track.op = Other

  -- transitions
  always (
    (some f: File | delete[f]) or 
    (some f: File | restore[f]) or 
    emptyTrash or other
  )
}

------------------------------
-- Expected system properties
------------------------------

-- Every restored file was once deleted
assert restoreAfterDelete {
  always (all f : File | restore[f] implies once delete[f])
}
check restoreAfterDelete for 8 steps

-- If the trash contains all files and is emptied
-- then no files will ever exist afterwards
assert deleteAll {
  always ((File in Trash and emptyTrash) implies after always no File)
}
check deleteAll for 8 steps

-- The set of files never increases
assert noNewFiles {
  always File' in File
}
check noNewFiles for 8 steps

-- The set of files changes when the trash is emptied
assert emptyTrashDestroysFiles {
  always (emptyTrash implies File' != File)
}
check emptyTrashDestroysFiles for 8 steps

-- The set of files changes *only* when the trash is emptied
assert onlyEmptyTrashDestroysFiles {
  always (File' != File implies emptyTrash)
}
check onlyEmptyTrashDestroysFiles for 8 steps

-- If no files are ever deleted the trash cannot be emptied anymore
assert noEmptyWithNoDelete {
  always (once (some f: File | delete[f]) or not emptyTrash)
}
check noEmptyWithNoDelete for 8 steps

-- Restoring a file immediately after deleting it undoes the delete
assert restoreUndoesDelete {
  always (
    (some f: File | delete[f] and after restore[f]) implies Trash'' = Trash
  )
}
check restoreUndoesDelete for 8 steps




