Division by 2 in homotopy type theory
=====================================

This is a formalization in cubical [Agda](https://wiki.portal.chalmers.se/agda/)
of division by two in type theory, as [detailed in this
article](http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_div2.pdf).

The main result here is that

> `A × 2 ≃ B × 2`

implies

> `A ≃ B`

where `2` is a type with two elements (e.g. the booleans).

The proof is based on the explanation of given in Doyle and Conway's _[Division
by three](https://arxiv.org/abs/math/0605779)_.
