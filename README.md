# CS263 Final Project

The final team project for SJTU course CS 263, Spring 2020, *Programming Languages*.

Part of the codes used in this project is borrowed from class materials.



## Topics: Equivalence among 3 denotational semantics and small step semantics

> In this task, you should first prove **a general theorem which can be used to prove an equivalence between two recursively defined semantics**, and **another general theorem which can be used to prove an equivalence between a recursively defined program semantics and a small step semantics**.
>
> Then, you need to prove the equivalence among three denotational program semantics and a small step semantics.



## Compilation Order

1. ImpExt4.v
2. Imp3.v
3. DenotationalSemantics.v
4. DenotationalSemEquiv.v
5. SmallStepSemantics.v
6. SmallStepSemEquiv.v



## Proof Idea

- DenotationalSemantics.v

  We define three denotational program semantics, which are based on the project instruction. However we also make some slight modification.

  First, we define a general recursively defined denotational semantic, which has five basic commands *(skip, assignment, sequence, if, while)*. A program's semantic is recursively defined on the semantic of the five basic commands.

  Then, we give the definition of three concrete denotational semantics after defining the semantics of five basic commands.

- DenotationalSemEquiv.v

  We raise and prove a general theorem to prove an equivalence between two recursively defined semantics. We use it to prove the equivalence between three denotational semantics defined in DenotationalSemantics.v.

  First, we define the equivalence of five basic commands between two recursively defined semantics.

  Next, we put forward and prove the general theorem for equivalence between them.

  Then, we prove the equivalence of five basic commands between two concrete semantics defined in DenotationalSemantics.v.

  At last, we apply the general theorem and finish the proof.

- SmallStepSemantics.v

  We define two small step semantics, one corresponds to binary denotational semantics, another for ternary denotational semantics.
  
  Furthermore, we introduced the concept "Middle parameter", to, in some sense, simulate the step count (or trace) in the small step execution process.
  
  It is obvious that the 2 small step semantics are equivalent, since their definition only differs in one extra bool variable to denote whether it is necessary to add one step count (or trace). The other part of definition of the 2 semantics is exactly the same to each other.
  
- SmallStepSemEquiv.v

    We prove the equivalence between binary denotational semantics and small step semantics, and ternary denotational semantics and small step semantics respectively. 

    We prove the equivalence in 2 directions. For denotation -> small step direction, we mainly prove by induction and congruence rule. For small step -> denotation direction, we prove by the idea that any small step from a pair *(c1, st1)* to *(c2, st2)* will not change the result of its denotation.

    As it takes an amount of time to find the final result, here we note that the final theorem of the equivalence of binary semantics is at **Line 579**, and ternary semantics is at **Line 845**.

    

## Contributor

Xue Huangzhen [@xuehzjing](https://github.com/xuehzjing)

Ge Qirui [@iamgqr](https://github.com/iamgqr)

Wang Kerong [@FallCicada](https://github.com/FallCicada)

