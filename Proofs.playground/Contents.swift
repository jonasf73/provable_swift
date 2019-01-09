//: ## IF IT BUILDS, IT'S PROVEN!
//: *(only rule: don't use the standard lib)*
//:
//: Proving a "proposition" `P` is equivalent to writing some code that is able to create an element of type `P`.
//:
//: So if you can write any of the following declarations and have Swift be able to compile with no errors and warnings, you "proved" `P`.
//: ```swift
//: let _ : P = ...
//: func f() -> P { ... }
//: ```
//: Also, if you can write a function like:
//: ```swift
//: func f(_: P) -> Q {}
//: ```
//: then, you "proved" `P ⟹ Q` since you can construct an element of `Q` from any element of `P` using this function.
//:
//: **Note** that the actual implementation is irrelevant as long as it compiles.
//: Same as a proof: how long, unreadable or inneficient it is, if it is correct, the important thing is that the result has been proven.
//:
// we might need that
func compose<P,Q,R>(_ f : @escaping (Q) -> R, _ g : @escaping (P) -> Q) -> ((P) -> R) {
    return { p in f(g(p)) }
}

//: **`True`** being… true, it's easy to get an element of that type
enum True {
    case true_is_true
}

//: **`False`** being… false, it's pretty hard to get any element for that type
enum False {
}

//: Proving `P ⟹ Q` means being able to write a function `(P) -> Q` that builds
typealias IMP<P,Q> = (P) -> Q

//: ### Trivial theorem
//: `∀ P, P ⟹ P`
func trivial<P>(p : P) -> P {
    return p
}

//: ### Forget one premise
//: `∀ P Q, P ⟹ Q ⟹ P`
//:
//: **Note** that `P ⟹ Q ⟹ R` should be read `P ⟹ (Q ⟹ R)`. If `P` is proven, then if `Q` is also proven then you proved `R`.
func forget<P,Q>() -> IMP<P,IMP<Q,P>> {
    return { p in { q in p }}
}

//: ### Syllogisms
//: `∀ P Q: P ⟹ (P ⟹ Q) ⟹ Q`
func induction<P,Q>() -> IMP<P,IMP<IMP<P,Q>,Q>> {
    return { p in { pq in pq(p) }}
}

//: `∀ P Q R, (P ⟹ Q) ⟹ (Q ⟹ R) ⟹ (Q ⟹ R)`
func imp_trans<P,Q,R>() -> IMP<IMP<P,Q>,IMP<IMP<Q,R>,IMP<P,R>>> {
    return { pq in { qr in compose(qr, pq) }}
}

//:  `∀ P Q R, (P ⟹ Q ⟹ R) ⟹ (Q ⟹ P ⟹ R)`
func imp_comm<P,Q,R>() -> IMP<IMP<P,IMP<Q,R>>,IMP<Q,IMP<P,R>>> {
    return { pqr in { q in { p in pqr(p)(q) }}}
}

//: If you can prove False, you can prove anything!
//: `∀ P, False -> P`
func False_proves_anything<P>() -> ((False) -> P) {
    return { ff in switch ff { } }
}

//: ### Not construct
//: **`~P`** is defined as `P ⟹ False`. This means that if you know `~P` and you can prove `P` then
//: you can prove `False` and by extension, you can prove anything.
typealias NOT<P> = IMP<P,False>

//: `∀ P, P ⟹ ~~P`
//:
//: **Note** that proving `~~P ⟹ P` requires `P` to be decidable.
func P_imp_not_not_P<P>() -> IMP<P,NOT<NOT<P>>> {
    return { p in { np in np(p) }}
}

//: ### Reductio ad absurdum
//:
//: `∀ P, P ⟹ ~P ⟹ False`
func absurd<P>() -> IMP<P,IMP<NOT<P>,False>> {
    return { p in { notP in notP(p) }}
}

//: ### Or construct
enum OR<P,Q> {
    case left(P)
    case right(Q)
}

//: `True ∨ False` is provable
func true_or_false() -> OR<True,False> {
    return .left(.true_is_true)
}

//: `∀ P Q, P ⟹ P ∨ Q`
func or_intro_l<P,Q>() -> ((P) -> OR<P,Q>) {
    return { p in .left(p) }
}

//: `∀ P Q, Q ⟹ P ∨ Q`
func or_intro_r<P,Q>() -> ((Q) -> OR<P,Q>) {
    return { q in .right(q) }
}

//: **note**: `or_intro_l` and `or_intro_r` can be used to break down
//: propositions of the form `x ∨ y ⟹ z in x ⟹ z and y ⟹ z`

//: `∀ P Q R, (P ⟹ R) ⟹ (Q ⟹ R) ⟹ ((P ∨ Q) ⟹ R)`
func or_ind<P,Q,R>() -> IMP<IMP<P,R>,IMP<IMP<Q,R>,IMP<OR<P,Q>,R>>> {
    return { pr in { qr in { pq in switch pq { case .left(let p): return pr(p);  case .right(let q): return qr(q) } } } }
}

//: **note**: `or_ind` allows re-construction `x ∨ y ⟹ z`
//: if you have `x ⟹ z` and `y ⟹ z`

//: `∀ P Q, P ∨ Q -> Q ∨ P`
func or_comm<P,Q>() -> IMP<OR<P,Q>,OR<Q,P>> {
    return { pq in
        switch pq {
        case .left(let p): return .right(p)
        case .right(let q): return .left(q)
        }
    }
}

//: `∀ P Q R, (P ∨ Q) ∨ R ⟹ P ∨ (Q ∨ R)`
func or_assoc_left<P,Q,R>() -> IMP<OR<OR<P,Q>,R>,OR<P,OR<Q,R>>> {
    return { pqr in
        switch pqr {
        case .left(let pq):
            switch pq {
            case .left(let p) : return .left(p)
            case .right(let q) : return .right(.left(q))
            }
        case .right(let r): return .right(.right(r))
        }
    }
}


//: `∀ P Q R, P ∨ (Q ∨ R) ⟹ (P ∨ Q) ∨ R`
func or_assoc_right<P,Q,R>() -> IMP<OR<P,OR<Q,R>>,OR<OR<P,Q>,R>> {
    // just to test the whole thing, let's do some proof based only on Swift typesystem and previous proofs
    // we use the proof of or_assoc_left with some permutation of P, Q and R and use commutativity of ∨
    return or_ind()(compose(compose(compose(or_comm(), compose(or_assoc_left(), or_intro_l())), or_comm()), or_intro_l()))(or_ind()(compose(or_comm(), compose(or_assoc_left(), or_intro_r())))(compose(compose(compose(or_comm(), compose(or_assoc_left(), or_intro_l())), or_comm()), or_intro_r())))
}

//: `∀ P, P ⟹ P ∨ P`
func P_imp_P_or_P<P>() -> IMP<P,OR<P,P>> {
    return { p in .left(p) }
}

//: `∀ P, P ∨ P ⟹ P`
func P_or_P_imp_P<P>() -> IMP<OR<P,P>,P> {
    return { orPP in
        switch orPP {
        case .left(let p): return p
        case .right(let p): return p
        }
    }
}

//: ### And construct
typealias AND<P,Q> = (P,Q)

//: `∀ P Q, P ⟹ Q ⟹ P ∧ Q`
func conj<P,Q>() -> IMP<P,IMP<Q,AND<P,Q>>> {
    return { p in return { q in (p,q) }}
}

//: `∀ P Q, P ∧ Q ⟹ P`
func split_and_left<P,Q>() -> IMP<AND<P,Q>,P> {
    return { pq in pq.0 }
}

//: `∀ P Q, P ∧ Q ⟹ Q`
func split_and_right<P,Q>() -> IMP<AND<P,Q>,Q> {
    return { pq in pq.1 }
}

//: `∀ P Q R, (P ⟹ Q) ⟹ (P ⟹ R) ⟹ (P ⟹ P ∧ R)`
func and_join<P,Q,R>() -> IMP<IMP<P,Q>,IMP<IMP<P,R>,IMP<P,AND<Q,R>>>> {
    return { pq in { pr in { p in return (pq(p), pr(p)) }}}
}

//: `∀ P Q, P ∧ Q ⟹ Q ∧ P`
func and_comm<P,Q>() -> IMP<AND<P,Q>,AND<Q,P>> {
    return and_join()(split_and_right())(split_and_left())
}

//: `∀ P Q R, (P ⟹ Q) ⟹ (P ∧ R ⟹ Q ∧ R)`
func imp_compat_with_and<P,Q,R>() -> IMP<IMP<P,Q>,IMP<AND<P,R>,AND<Q,R>>> {
    return { pq in return and_join()(compose(pq, split_and_left()))(split_and_right()) }
}

//: `∀ P Q R, (P ∧ Q) ∧ R ⟹ P ∧ (Q ∧ R)`
func and_assoc_left<P,Q,R>() -> IMP<AND<AND<P,Q>,R>,AND<P,AND<Q,R>>> {
    // this beautiful proof is also a courtesy of Swift type inference
    return and_join()(compose(split_and_left(), split_and_left()))(and_join()(compose(split_and_right(), split_and_left()))(split_and_right()))
}

//: `∀ P Q R, P ∧ (Q ∧ R) ⟹ (P ∧ Q) ∧ R`
func and_assoc_right<P,Q,R>() -> IMP<AND<P,AND<Q,R>>,AND<AND<P,Q>,R>> {
    // and once again. It's a bit of a pain to find it. Maybe we need some sort of proof assistant? We might even give it an other bird name?
    return and_join()(and_join()(split_and_left())(compose(split_and_left(), split_and_right())))(compose(split_and_right(), split_and_right()))
}

//: Rephrasing imp_trans theorem using ∧
//:
//: `∀ P Q R, (P ⟹ Q) ∧ (Q ⟹ R) ⟹ (P ⟹ R)`
func P_imp_Q_and_Q_imp_R_imp_P_imp_R<P,Q,R>() -> IMP<AND<IMP<P,Q>,IMP<Q,R>>,IMP<P,R>> {
    // note that we use the proof of imp_trans
    return { pqr in imp_trans()(pqr.0)(pqr.1) }
}

//: ### Equivalence construct
typealias IFF<P,Q> = AND<IMP<P,Q>,IMP<Q,P>>

//: `∀ P, P ⟺ P`
func iff_refl<P>() -> IFF<P,P> {
    return (trivial,trivial)
}

//: `∀ P Q R, (P ⟺ Q) ⟹ (Q ⟺ R) ⟹ (P ⟺ R)`
func iff_trans<P,Q,R>() -> IMP<IFF<P,Q>,IMP<IFF<Q,R>, IFF<P,R>>> {
    return { iffPQ in { iffQR in (compose(iffQR.0, iffPQ.0), compose(iffPQ.1, iffQR.1)) } }
}

//: `∀ P Q, (P ⟺ Q) ⟹ (Q ⟺ P)`
func iff_comm<P,Q>() -> IMP<IFF<P,Q>,IFF<Q,P>> {
    // neat simple proof : ∧ is symetric, Qed.
    // isn't it a beautiful proof?
    return and_comm()
}

//: `∀ P Q, (P ⟺ Q) ⟹ (P ⟹ Q) ∧ (Q ⟹ P)`
func iff_and<P,Q>() -> IMP<IFF<P,Q>,AND<IMP<P,Q>,IMP<Q,P>>> {
    // as is this one…
    return trivial
}

//: `∀ P Q, (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P)`
func iff_equiv_and_imp<P,Q>() -> IFF<IFF<P,Q>,AND<IMP<P,Q>,IMP<Q,P>>> {
    // as is this one…
    return (trivial, trivial)
}

//: `∀ P Q R, (P ∨ Q) ∨ R <⟹ P ∨ (Q ∨ R)`
func or_assoc<P,Q,R>() -> IFF<OR<OR<P,Q>,R>,OR<P,OR<Q,R>>> {
    return (or_assoc_left(), or_assoc_right())
}

//: `∀ P Q R, (P ∧ Q) ∧ R ⟺ P ∧ (Q ∧ R)`
func and_assoc<P,Q,R>() -> IFF<AND<AND<P,Q>,R>,AND<P,AND<Q,R>>> {
    return (and_assoc_left(), and_assoc_right())
}

//: ### Decidability
//: A proposition `P` is **decidable** if you can find either a proof of `P` or a proof of `~P`
typealias DECIDABLE<P> = OR<P,NOT<P>>

//: `∀ P, P is decidable ⟹ ~~P ⟹ P`
func not_not_P_imp_P<P>() -> IMP<DECIDABLE<P>,IMP<NOT<NOT<P>>,P>> {
    return { decP in
        switch (decP) {
        case .left(let p):
            return { nnP in p }
        case .right(let notP):
            // if ~P then ~~P ⟹ False
            return { nnP in nnP(notP) }
        }
    }
}

//: ### Beyond Swift Type System
//: At this point, the Swift Type System is pretty limited. To express more complex propositionts you need an elaborate type system where types can be dependent.
//:
//: Swift Type System only allows dependent type through generics which act as universal quantifiers.
//:
//: Also there is one tiny litte **second rule** to the game: though the implementation does not really matter, still **it must** end**.
//:
//: You can't write functions that run forever. Alas (of course), the Swift compiler can't enforce this as this can't be decided. 😔
//: That's why real proof assistants enforces rules on what "programs" you can't write that guarantees that they will always end.
//:
//: With a fully Turing complete language like Swift, you can do dirty tricks like:
//:
//: ```swift
//: func everything_is_possible<P>() -> P {
//:    return everything_is_possible()
//: }
//: ```
//:
//: though this particular trick is detected by the Swift compiler which emits a warning.
//:
//: "Fortunately", this one does not:

func everything_is_possible<P>() -> P {
    while(true) {
    }
}

//: #### so yes, anything is possible!


