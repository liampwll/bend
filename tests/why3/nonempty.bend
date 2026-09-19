# why3: Reject no finite inhabitants
type Bottom is Data:
  Roll{value: Bottom}

law vacuous:
  for x: Bottom
  {x == x : Bottom}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
