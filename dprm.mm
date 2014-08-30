$[ set.mm $]

$v coefSpace numVariables exponents numTerms terms $.
vcoefSpace $f set coefSpace $.
vnumVariables $f set numVariables $.
vexponents $f set exponents $.
vnumTerms $f set numTerms $.
vterms $f set terms $.
$c MVMono MVPoly $.


${
    $( Multivariate polynomials over ` CC ` .  Should generalize to any ring soon.  These are real polynomial functions, not formal polynomials; this, for instance, we do not distinguish the Froebnius polynomial on a prime field from the identity. $)
    $( A multivariate monomial is a function of the form C a b ... f
    $d numVariables coefSpace c exponents x f k $.
    cmvmono $a class MVMono $.
    df-mvmono $a |- MVMono = ( numVariables e. NN0 , coefSpace e. ~P CC |->
        { f e. ( CC ^m ( CC ^m ( 1 ... numVariables ) ) ) |
            E. c e. coefSpace
            E. exponents e. ( NN0 ^m ( 1 ... numVariables ) )
            A. x e. ( CC ^m ( 1 ... numVariables ) )
            ( f ` x ) = ( c * prod_ k e. ( 1 ... numVariables ) * ( ( x ` k ) ^ ( exponents ` k ) ) )
        }
    ) $.
    $)

    $( Warmup version: limited to ZZ $)
    cmvzmonof $a class MVZMonoF $.
    $d n f x y z k $.
    df-mvzmonof $a |- MVZMonoF = ( n e. NN0 |-> { f e. ( ZZ ^m ( ZZ ^m ( 1 ... n ) ) ) | E. x e. ZZ E. y e. ( NN0 ^m ( 1 .. n ) ) A. z e. ( ZZ ^m ( 1 ... n ) ) ( f ` z ) = x x. prod_ k e. ( 1 ... n ) x. ( ( z ` k ) ^ ( y ` k ) ) } ) $.
$}

${
    $( A multivariate polynomial is a finite sum of monomials.

    cmvpoly $a class MVPoly $.
    $d numVariables coefSpace f numTerms terms x k $.
    df-mvpoly $a |- MVPoly = ( numVariables e. NN0 , coefSpace e. ~P CC |->
        { f e. ( CC ^m ( CC ^m ( 1 ... numVariables ) ) ) |
            E. numTerms e. NN0
            E. terms e. ( ( numVariables MVMono coefSpace ) ^m ( 1 ... numTerms ) )
            A. x e. ( CC ^m ( 1 ... numVariables ) )
            ( f ` x ) = prod_ k e. ( 1 ... numTerms ) + ( ( terms ` k ) ` x )
        }
    ) $.
    $)
$}

$( let's start smaller.  much smaller
    df-polyN = ( numVariables e. NN0 , coefSpace e. ~P CC |-> |^| { 
$)

${
    scalar-mvmono-test0.1 $p |- ( ( ( CC ^m ( 1 ... 2 ) ) X. { 3 } ) e. {  } ) $= ? $.
    scalar-mvmono-test0 $p |- ( ( ( CC ^m ( 1 ... 2 ) ) X. { 3 } ) e. ( 2 MVMono NN ) ) $= ? $.
$}

${
    $(
        A scalar is a MVMono

expand definition with 
    $)

    scalar-mvmono.1 $e |- A e. ~P CC $.
    scalar-mvmono $p |- ( ( c e. A /\ n e. NN0 ) -> ( ( ( CC ^m ( 1 ... n ) ) X. { c } ) e. ( n MVMono A ) ) ) $= ? $.
$}
