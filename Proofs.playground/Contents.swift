//: ## IF IT BUILDS, IT'S PROVEN!
//: *(you are not allowed to use the standard lib)*
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
//: Or rephrased in logical terms: if you have a proof of `P`, you get a proof of `Q`.
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

//: `∀ P Q, Q ⟹ P ⟹ P`
func forget2<P,Q>() -> IMP<Q,IMP<P,P>> {
    return { q in trivial }
}

//: ### Modus ponens
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

//: ### Ex falso, quodlibet
//: If you can prove False, you can prove anything!
//:
//: `∀ P, False -> P`
func False_proves_anything<P>() -> ((False) -> P) {
    return { non_existing_element_of_False in switch non_existing_element_of_False { } }
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

//: `∀ P Q, (P ⟹ Q) ⟹ (~Q ⟹ ~P)`
//:
//: **Note** that the equivalence only works if `Q` is decidable.
func contrapositive_right<P,Q>() -> IMP<IMP<P,Q>,IMP<NOT<Q>,NOT<P>>>  {
    return { impPQ in { notQ in { p in notQ(impPQ(p)) } } }
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

//: `∀ P Q, ~P -> ~Q -> ~(P ∨ Q)`
func not_not_or<P,Q>() -> IMP<NOT<P>,IMP<NOT<Q>,NOT<OR<P,Q>>>> {
    return { notP in { notQ in { orPQ in switch orPQ { case .left(let p): return notP(p); case .right(let q): return notQ(q) }}}}
}

//: ### And construct
typealias AND<P,Q> = (P,Q)

//: `∀ P Q, P ⟹ Q ⟹ P ∧ Q`
func conj<P,Q>() -> IMP<P,IMP<Q,AND<P,Q>>> {
    return { p in { q in (p,q) }}
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
    return { pq in { pr in { p in (pq(p), pr(p)) }}}
}

//: `∀ P Q, P ∧ Q ⟹ Q ∧ P`
func and_comm<P,Q>() -> IMP<AND<P,Q>,AND<Q,P>> {
    return and_join()(split_and_right())(split_and_left())
}

//: `∀ P Q R, (P ⟹ Q) ⟹ (P ∧ R ⟹ Q ∧ R)`
func imp_compat_with_and<P,Q,R>() -> IMP<IMP<P,Q>,IMP<AND<P,R>,AND<Q,R>>> {
    return { pq in and_join()(compose(pq, split_and_left()))(split_and_right()) }
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

//: `∀ P Q, ~P ⟹ ~(P ∧ Q)`
func not_P_imp_not_P_and_Q<P,Q>() -> IMP<NOT<P>,NOT<AND<P,Q>>> {
    return { notP in { pAndQ in notP(pAndQ.0) } }
}

//: `∀ P Q, ~Q ⟹ ~(P ∧ Q)`
func not_Q_imp_not_P_and_Q<P,Q>() -> IMP<NOT<Q>,NOT<AND<P,Q>>> {
    return { notQ in { pAndQ in notQ(pAndQ.1) } }
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

//: `∀ P Q, P is decidable ⟹ Q is decidable ⟹ P ∨ Q is decidable`
func decidable_compat_or<P,Q>() -> IMP<DECIDABLE<P>,IMP<DECIDABLE<Q>, DECIDABLE<OR<P,Q>>>> {
    return { dp in
        { dq in
            switch (dp) {
            case .left(let p):
                return .left(.left(p))
            case .right(let notP):
                switch dq {
                case .left(let q):
                    return .left(.right(q))
                case .right(let notQ):
                    return .right(not_not_or()(notP)(notQ))
                }
            }
        }
    }
}

//: `∀ P Q, P is decidable ⟹ Q is decidable ⟹ P ∧ Q is decidable`
func decidable_compat_and<Q,P>() -> IMP<DECIDABLE<P>,IMP<DECIDABLE<Q>, DECIDABLE<AND<P,Q>>>> {
    return { dp in
        { (dq : DECIDABLE<Q>) in
            switch(dp) {
            case .left(let p):
                switch dq {
                case .left(let q):
                    return .left((p , q))
                case .right(let notQ):
                    return .right(not_Q_imp_not_P_and_Q()(notQ))
                }
            case .right(let notP):
                return .right(not_P_imp_not_P_and_Q()(notP))
            }
        }
    }
}

//: `∀ P Q, (Q is decidable) ⟹ (~Q ⟹ ~P) ⟹ (P ⟹ Q)`
func contrapositive_left<P,Q>() -> IMP<DECIDABLE<Q>,IMP<IMP<NOT<Q>,NOT<P>>,IMP<P,Q>>>  {
    return { decQ in
        { not_Q_imp_not_P in
            { p in
                switch (decQ) {
                case .left(let q):
                    return q
                case .right(let notQ):
                    // not_Q_imp_not_P(notQ)(p) never returns
                    not_Q_imp_not_P(notQ)(p)
                }
            }
        }
    }
}

//: `∀ P Q, (Q is decidable) ⟹ (~Q ⟹ ~P) ⟺ (P ⟹ Q)`
func contrapositive<P,Q>() -> IMP<DECIDABLE<Q>,IFF<IMP<NOT<Q>,NOT<P>>,IMP<P,Q>>>  {
    return { decQ in (contrapositive_left()(decQ), contrapositive_right()) }
}

//: ### Beyond Swift Type System
//: At this point, the Swift Type System is pretty limited. To express more complex propositionts you need an elaborate type system where types can be dependent.
//:
//: Swift Type System only allows dependent type through generics which act as universal quantifiers.
//:
//: Also there is one tiny litte **hidden rule** to the game: though the implementation does not really matter, still **it must end** (though not necessarily return!).
//:
//: You can't write functions that run forever. Alas, the Swift compiler can't enforce this as this is famously undecidable. 😔
//:
//: That's why real proof assistants enforce rules on what "programs" you can write that guarantees that they will always end.
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
//:
//: ```swift
//: func everything_is_possible<P>() -> P {
//:     while(true) {
//:     }
//: }
//: ```
//:
//: We can use this quirk to create "axioms":

func axiom<P>() -> P {
    while(true) {
    }
}

//: But with bad chosen axioms, you can create inconsistent theories.
//:
//: "*With great power…*"
//:
//: Still, you can use axioms to create specific theories:
//: ### Classical Logic
func classical_logic() {
    
//: *Excluded middle* axiom: all propositions are decidable
    func excluded_middle<P>() -> DECIDABLE<P> {
        return axiom()
    }
    
//: `~~P ⟹ P`
    func not_not_P_imp_P_classical<P>() -> IMP<NOT<NOT<P>>,P> {
        return not_not_P_imp_P()(excluded_middle())
    }
    
//: `∀ P Q, (~Q ⟹ ~P) ⟺ (P ⟹ Q)`
    func contrapositive_classical<P,Q>() -> IFF<IMP<NOT<Q>,NOT<P>>,IMP<P,Q>>  {
        return contrapositive()(excluded_middle())
    }
}
