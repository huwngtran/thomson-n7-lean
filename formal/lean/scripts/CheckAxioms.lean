import ThomsonN7.Solution
/-! Axiom check for the two theorems. Expected: each depends only on
    `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms ThomsonN7.thomson_seven
#print axioms ThomsonN7.thomson_seven_unique
#check @ThomsonN7.thomson_seven
#check @ThomsonN7.thomson_seven_unique
