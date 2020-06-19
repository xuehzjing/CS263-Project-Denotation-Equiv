# CS263 Final Project

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

## TODO

- Prove the theorem which can be used to prove the equivalence between a recursively defined semantics and a small step semantics.

## Done

- Prove a general theorem used to prove an equivalence between two recursively defined semantics.
- Prove the equivalence between three denotational  semantics.
- Prove the equivalence between three denotational semantics ( *plain binary relation, one with time, one with trace* ) and a small step semantics.

## Proof Idea

- DenotationalSemantics.v

  We define three denotational program semantics, which are based on the project instruction. However we also make some modification.

  First, we define a general recursively defined denotational semantic, which has five basic commands *(skip, assignment, sequence, if, while)*. A program's semantic is recursively defined on the semantic of the five basic commands.

  Then, we give the definition of three concrete denotational semantics after defining the semantics of five basic commands.

- DenotationalSemEquiv.v

  - Denotation

    We raise and prove a general theorem to prove an equivalence between two recursively defined semantics. We use it to prove the equivalence between three denotational semantics defined in DenotationalSemantics.v.

    First, we define the equivalence of five basic commands between two recursively defined semantics.

    Next, we put forward and prove the general theorem for equivalence between them.

    Then, we prove the equivalence of five basic commands between two concrete semantics defined in DenotationalSemantics.v.
  
    At last, we apply the general theorem and finish the proof.
  
  - Denotation V.S. Small Step
  
    We give a general theorem and use it to prove the equivalence between denotational semantics and small step semantics.

## Contributor

Xue Huangzhen [@xuehzjing](https://github.com/xuehzjing)

Ge Qirui [@iamgqr](https://github.com/iamgqr)

Wang Kerong [@FallCicada](https://github.com/FallCicada)
