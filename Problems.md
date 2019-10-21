#### Problems

1. Because low's crash point is nondeterministic, high's crash result becomes nondeterministic.

   When proving BS in high -> low direction, we can't make sure low exec also crashes at the same point.

   - Solution: Add what oracle refines to to specs of low so you will know exactly the high oracle for that execution.

   

2. When high state changes during an exec, we can't prove new one is valid.

   - Solution: Remove validity relations from definitions.
     - Conclusion: Won't work because I need it for data noninterference. If I don't say state is valid but try to prove from an arbitrary state, it won't work.
   - ???

