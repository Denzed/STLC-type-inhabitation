## Description
A Haskell implementation of simply typed lambda calculus type inhabitation using generation trees breadth-first traversal.
### Algorithm
- I(gamma, alpha -> tau) => \x ^ alpha -> I(gamma + (x: alpha), tau) -- if we have an abstraction we generate __new__ variable x, assign type alpha to it and then inhabit tau
- I(gamma, alpha) => forall x ^ (alpha1 -> alpha2 -> ... alphan -> alpha) in gamma x I(gamma, alpha1) I(gamma, alpha2) ... I(gamma, alpha2) -- otherwise we find in context variables x of type that has alpha as the return type and inhabit its arguments -- the result will be an application of arguments to that x
## Build
To build the project you will need Glasgow Haskell Compiler (ghc):
`ghc Main.hs` --- to get an executable `Main`
## Usage
The program uses text interface for the sake of simplicity. 
First line -- type to inhabit. 
Second -- wanted amount of terms (could be less than specified number if the family of terms is not that rich). It was added as a workaround to the possible infiniteness of the result (Church numbers in the example)
```
Main
Please, enter the type to inhabit:
(a -> a) -> a -> a
Please, enter the desired number of terms
to limit the result with (leave blank if you want all):
3
[\x1 x2 -> x2,\x1 x2 -> x1 x2,\x1 x2 -> x1 (x1 x2)]
```
