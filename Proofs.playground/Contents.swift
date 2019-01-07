//: ## IF IT BUILDS, IT'S PROVEN!
//: *(only rule: don't use the standard lib)*

//: Being able to write a function `() -> P` that compiles is equivalent to proving the "proposition" `P`

// we might need that
func compose<P,Q,R>(_ f : @escaping IMP<Q,R>, _ g : @escaping IMP<P,Q>) -> IMP<P,R> {
    return { p in f(g(p)) }
}

//: A "proof" of a type is a function that have no premises (i.e. no parameter)
//: and returns an element of the type to be proven.

//: `True` being... true, it's easy to get an element of that type
enum True {
    case true_is_true
}

//: `False` being... false, it's pretty hard to get any element for that type
enum False {
}

//: Proving `P ⟹ Q` means being able to write a function `(P) -> Q` that builds
typealias IMP<P,Q> = (P) -> Q

//: ### Trivial theorem
//: ∀ P, P ⟹ P
func trivial<P>() -> IMP<P,P> {
    return { p in p }
}

//: ∀ P Q R, (P ⟹ Q) ⟹ (Q ⟹ R) ⟹ (Q ⟹ R)
func imp_trans<P,Q,R>() -> IMP<IMP<P,Q>,IMP<IMP<Q,R>,IMP<P,R>>> {
    return { (pq : @escaping IMP<P,Q>) in { (qr : @escaping IMP<Q,R>) in compose(qr, pq) }}
}

//:  ∀ P Q R, (P ⟹ Q ⟹ R) ⟹ (Q ⟹ P ⟹ R)
func imp_comm<P,Q,R>() -> IMP<IMP<P,IMP<Q,R>>,IMP<Q,IMP<P,R>>> {
    return { (pqr : @escaping IMP<P,IMP<Q,R>>) in { (q: Q) in { (p: P) in pqr(p)(q) }}}
}

//: If you can prove False, you can prove anything!
//: ∀ P, False -> P
func False_ind<P>(ff: False) -> P {
    switch ff {
        // no cases here
    }
}

//: ~P is defined as P ⟹ False. This means that if you know ~P and you can prove P then
//: you can prove False and by extension, you can prove anything.
typealias NOT<P> = IMP<P,False>

//: Reductio ad absurdum
//: ∀ P, P ⟹ ~P ⟹ False
func absurd<P>() -> IMP<P,IMP<NOT<P>,False>> {
    return { (p : P) in { (notP : NOT<P>) in notP(p) }}
}

//: ∀ P, P ⟹ ~~P
//:
//: **note** : proving ~~P ⟹ P requires P to be decidable.
func P_imp_not_not_P<P>() -> IMP<P,NOT<NOT<P>>> {
    return { (p : P) in { (np : NOT<P>) in np(p) }}
}

//: ### Or construct
enum OR<P,Q> {
    case left(P)
    case right(Q)
}

//: True ∨ False is provable
func true_or_false() -> OR<True,False> {
    return .left(.true_is_true)
}

//: ∀ P Q, P ⟹ P ∨ Q
func or_intro_l<P,Q>(p : P) -> OR<P,Q> {
    return .left(p)
}

//: ∀ P Q, Q ⟹ P ∨ Q
func or_intro_r<P,Q>(q : Q) -> OR<P,Q> {
    return .right(q)
}

//: **note**: `or_intro_l` and `or_intro_r` can be used to break down
//: propositions of the form `x ∨ y ⟹ z in x ⟹ z and y ⟹ z`

//: ∀ P Q R, (P ⟹ R) ⟹ (Q ⟹ R) ⟹ ((P ∨ Q) ⟹ R)
func or_ind<P,Q,R>() -> IMP<IMP<P,R>,IMP<IMP<Q,R>,IMP<OR<P,Q>,R>>> {
    return { (pr : @escaping (P) -> R) in
        { (qr : @escaping (Q) -> R) in
            { (pq : OR<P,Q>) in
                switch pq {
                case .left(let p): return pr(p)
                case .right(let q): return qr(q)
                }
            }
        }
    }
}

//: **note**: `or_ind` allows re-constructin `x ∨ y ⟹ z`
//: if you have `x ⟹ z` and `y ⟹ z`

//: ∀ P Q, P ∨ Q -> Q ∨ P
func or_comm<P,Q>() -> IMP<OR<P,Q>,OR<Q,P>> {
    return { (pq : OR<P,Q>) in
        switch pq {
        case .left(let p): return .right(p)
        case .right(let q): return .left(q)
        }
    }
}

//: ∀ P Q R, (P ∨ Q) ∨ R ⟹ P ∨ (Q ∨ R)
func or_assoc_left<P,Q,R>() -> IMP<OR<OR<P,Q>,R>,OR<P,OR<Q,R>>> {
    return { (pqr: OR<OR<P,Q>,R>) in
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


//: ∀ P Q R, P ∨ (Q ∨ R) ⟹ (P ∨ Q) ∨ R
func or_assoc_right<P,Q,R>() -> IMP<OR<P,OR<Q,R>>,OR<OR<P,Q>,R>> {
    // we use the proof of or_assoc_left with some permutation of P, Q and R and use commutativity of ∨
    let a : IMP<OR<OR<R,P>,Q>,OR<R,OR<P,Q>>> = or_assoc_left() // (R ∨ P) ∨ Q ⟹ R ∨ (P ∨ Q)
    // break down the (...) ∨ R ⟹ ...
    // left
    let b = compose(a, or_intro_l) // R ∨ P ⟹ R ∨ (P ∨ Q)
    let c = compose(compose(or_comm(), b), or_comm()) // P ∨ R ⟹ R ∨ (P ∨ Q)
    
    // right
    let d = compose(c, or_intro_r) // R ⟹ (P ∨ Q) ∨ R
    // break further
    let e = compose(c, or_intro_l) // P ⟹ (P ∨ Q) ∨ R
    let f = compose(a, or_intro_r) // Q ⟹ R ∨ (P ∨ Q)
    
    let g = compose(or_comm(), f) // Q ⟹ (P ∨ Q) ∨ R
    
    let h = or_ind()(g)(d)
    let i = or_ind()(e)(h)
    return i
}

//: ∀ P, P ⟹ P ∨ P
func P_imp_P_or_P<P>() -> IMP<P,OR<P,P>> {
    return { p in .left(p) }
}

//: ∀ P, P ∨ P ⟹ P
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

//: ∀ P Q, P ⟹ Q ⟹ P ∧ Q
func conj<P,Q>(p : P) -> ((Q) -> AND<P,Q>) {
    return { q in (p,q) }
}

//: ∀ P Q, P ∧ Q ⟹ Q ∧ P
func and_comm<P,Q>() -> IMP<AND<P,Q>,AND<Q,P>> {
    return { pq in (pq.1,pq.0) }
}

//: ∀ P Q, P ∧ Q ⟹ P
func split_and_left<P,Q>() -> IMP<AND<P,Q>,P> {
    return { pq in pq.0 }
}

//: ∀ P Q, P ∧ Q ⟹ Q
func split_and_right<P,Q>() -> IMP<AND<P,Q>,Q> {
    return compose(split_and_left(), and_comm())
}

//: ∀ P Q R, (P ∧ Q) ∧ R ⟹ P ∧ (Q ∧ R)
func and_assoc_left<P,Q,R>() -> IMP<AND<AND<P,Q>,R>,AND<P,AND<Q,R>>> {
    // expand AND<_,_> to show how easy it is to prove this one
    return { (pqr: ((P,Q),R)) in (pqr.0.0, (pqr.0.1, pqr.1)) }
}

//: ∀ P Q R, P ∧ (Q ∧ R) ⟹ (P ∧ Q) ∧ R
func and_assoc_right<P,Q,R>() -> IMP<AND<P,AND<Q,R>>,AND<AND<P,Q>,R>> {
    return { (pqr : (P,(Q,R))) in ((pqr.0, pqr.1.0), pqr.1.1) }
}

//: Rephrasing imp_trans theorem using ∧
//:
//: ∀ P Q R, (P ⟹ Q) ∧ (Q ⟹ R) ⟹ (P ⟹ R)
func P_imp_Q_and_Q_imp_R_imp_P_imp_R<P,Q,R>() -> IMP<AND<IMP<P,Q>,IMP<Q,R>>,IMP<P,R>> {
    // note that we use the demonstration of imp_trans
    return { P_imp_Q_and_Q_imp_R in imp_trans()(P_imp_Q_and_Q_imp_R.0)(P_imp_Q_and_Q_imp_R.1) }
}

//: ∀ P Q R, (P ⟹ Q) ⟹ (P ∧ R ⟹ Q ∧ R)
func imp_compat_with_and<P,Q,R>() -> IMP<IMP<P,Q>,IMP<AND<P,R>,AND<Q,R>>> {
    return { (pq : @escaping (P) -> Q) in { (andPR : AND<P,R>) in  (pq(andPR.0), andPR.1) } }
}

//: ### Equivalence construct
typealias IFF<P,Q> = AND<IMP<P,Q>,IMP<Q,P>>

//: ∀ P, P ⟺ P
func iff_refl<P>() -> IFF<P,P> {
    return (trivial(),trivial())
}

//: ∀ P Q R, (P ⟺ Q) ⟹ (Q ⟺ R) ⟹ (P ⟺ R)
func iff_trans<P,Q,R>() -> IMP<IFF<P,Q>,IMP<IFF<Q,R>, IFF<P,R>>> {
    return { (iffPQ : IFF<P,Q>) in { (iffQR : IFF<Q,R>) in (compose(iffQR.0, iffPQ.0), compose(iffPQ.1, iffQR.1)) } }
}

//: ∀ P Q, (P ⟺ Q) ⟹ (Q ⟺ P)
func iff_comm<P,Q>() -> IMP<IFF<P,Q>,IFF<Q,P>> {
    // neat simple proof : ∧ is symetric, Qed.
    return and_comm()
}

//: ∀ P Q, (P ⟺ Q) ⟹ (P ⟹ Q) ∧ (Q ⟹ P)
func iff_and<P,Q>() -> IMP<IFF<P,Q>,AND<IMP<P,Q>,IMP<Q,P>>> {
    // indeed, demonstration is trivial
    return trivial()
}

//: ∀ P Q, (P ⟺ Q) ⟺ (P ⟹ Q) ∧ (Q ⟹ P)
func iff_equiv_and_imp<P,Q>() -> IFF<IFF<P,Q>,AND<IMP<P,Q>,IMP<Q,P>>> {
    return (trivial(), trivial())
}

//: ∀ P Q R, (P ∧ Q) ∧ R ⟺ P ∧ (Q ∧ R)
func and_assoc<P,Q,R>() -> IFF<AND<AND<P,Q>,R>,AND<P,AND<Q,R>>> {
    return (and_assoc_left(), and_assoc_right())
}

//: ### Decidability
//: A proposition `P` is **decidable** if you can always find either a proof of `P` or a proof of `~P`
typealias DECIDABLE<P> = OR<P,NOT<P>>

//: ∀ P, P is decidable ⟹ ~~P ⟹ P
func not_not_P_imp_P<P>() -> IMP<DECIDABLE<P>,IMP<NOT<NOT<P>>,P>> {
    return { (decP : DECIDABLE<P>) in
        switch (decP) {
        case .left(let p):
            return { (nnP : NOT<NOT<P>>) in p }
        case .right(let notP):
            // if ~P then ~~P ⟹ False
            return { (nnP : NOT<NOT<P>>) in nnP(notP) }
        }
    }
}
