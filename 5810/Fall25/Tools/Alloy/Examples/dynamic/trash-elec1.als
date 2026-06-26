/* Exercise

1. Complete the definition of the predicates delete, restore and empty.
2. Using the Analyzer, show that the same file can be perpetually deleted.
3. Specify and verify the properties below stated for each empty
   assertion below.

**Use only the following temporal operators:**
  always, after, once, and primes (').
*/

var sig File {}
var sig Trash in File {}

abstract sig Operator {}
one sig Delete, Restore, EmptyTrash, Other extends Operator {}

one sig Track { var op: Operator }

-- Delete a file
pred delete[f : File] { Track.op' = Delete }

-- Restore a file from the trash
pred restore[f : File] { Track.op' = Restore } 

-- Empty the trash
pred emptyTrash { Track.op' = EmptyTrash }

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
 
}
check restoreAfterDelete for 8 steps

-- If the trash contains all files and is emptied
-- then no files will ever exist afterwards
assert deleteAll {

}
check deleteAll for 8 steps

-- The set of files never increases
assert noNewFiles {

}
check noNewFiles for 8 steps

-- The set of files changes when the trash is emptied
assert emptyTrashDestroysFiles {

}
check emptyTrashDestroysFiles for 8 steps

-- The set of files changes *only* when the trash is emptied
assert onlyEmptyTrashDestroysFiles {

}
check onlyEmptyTrashDestroysFiles for 8 steps

-- If no files are ever deleted the trash cannot be emptied anymore
assert noEmptyWithNoDelete {

}
check noEmptyWithNoDelete for 8 steps

-- Restoring a file immediately after deleting it undoes the delete
assert restoreUndoesDelete {

}
check restoreUndoesDelete for 8 steps




