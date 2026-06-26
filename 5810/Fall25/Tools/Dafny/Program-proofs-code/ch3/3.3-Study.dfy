method RequiredStudyTime(c: nat) returns (hours: nat)
  ensures hours <= 200

method Study(n: nat, h: nat)
  decreases n, h
{
  if h != 0 {
    // first, study for an hour, and then:
    Study(n, h - 1);
  } else if n == 0 {
    // you just finished course 0 -- woot woot, graduation time!
  } else {
    // find out how much studying is needed for the next course
    var hours := RequiredStudyTime(n - 1);
    // get started with course n-1:
    Study(n - 1, hours);
  }
}

method StudyPlan(n: nat)
  requires n <= 40
  decreases 40 - n
{
  if n == 40 {
    // done
  } else {
    var hours := RequiredStudyTime(n);
    Learn(n, hours);
  }
}

method Learn(n: nat, h: nat)
  requires n < 40
  decreases 40 - n, h
{
  if h == 0 {
    // done with class n; continue with the rest of the study plan
    StudyPlan(n + 1);
  } else {
    // some learning to take place here...
    Learn(n, h - 1);
  }
}
