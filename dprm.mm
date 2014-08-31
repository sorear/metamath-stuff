$[ set.mm $]

$c MVZMonoF $.


${
    $( Multivariate polynomials over ` CC ` .  Should generalize to any ring soon.  These are real polynomial functions, not formal polynomials; this, for instance, we do not distinguish the Froebnius polynomial on a prime field from the identity. $)

    $( Warmup version: limited to ZZ $)
    cmvzmonof $a class MVZMonoF $.
    $d n f x y z k $.
    df-mvzmonof $a |- MVZMonoF = ( n e. NN0 |-> { f e. ( ZZ ^m ( ZZ ^m ( 1 ... n ) ) ) | E. x e. ZZ E. y e. ( NN0 ^m ( 1 ... n ) ) A. z e. ( ZZ ^m ( 1 ... n ) ) ( f ` z ) = ( x x. prod_ k e. ( 1 ... n ) x. ( ( z ` k ) ^ ( y ` k ) ) ) } ) $.
$}

wu0 $p |- ( ( ZZ ^m ( 1 ... 0 ) ) X. { 0 } ) e. ( ZZ ^m ( ZZ ^m ( 1 ... 0 ) ) ) $= ( cc0 csn cz c1 cfz co cmap cxp wss wcel 0z snssi ax-mp zex ovex mapss wf elexi fconst snex elmap mpbir sselii ) ABZCDAEFZGFZGFZCUFGFZUFUDHZUDCIZUGUHIACJUJKACLMUDCUFNCUEGOZPMUIUGJUFUDUIQUFAACKRSUDUFUIATUKUAUBUC $.
${
    wu1.1 $e |- A e. _V $.
    wu1.2 $e |- B e. _V $.
    wu1.3 $e |- C e. _V $.
    $( a constant is a function $)
    wu1 $p |- ( B e. C -> ( A X. { B } ) e. ( C ^m A ) )  $= ( wcel csn cmap co cxp wss snssi mapss syl wf fconst snex elmap mpbir a1i sseldd ) BCGZBHZAIJZCAIJZAUDKZUCUDCLUEUFLBCMUDCAFDNOUGUEGZUCUHAUDUGPABEQUDAUGBRDSTUAUB $.  $( [30-Aug-2014] $)
$}
${
    $d u x $.
    $d a b $.
    wu8 $p |- ( u e. CC -> ( A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) -> u = 1 ) ) $= ( cv cc wcel cmul co wceq wa wral c1 wi ax-1cn ax-17 oveq2 id eqeq12d a1i simpl syld oveq1 anbi12d rcla4 ax-mp mulid1 syl simpr eqtr3d ex ) BCZDEZUJACZFGZULHZULUJFGZULHZIZADJZUJKFGZKHZKUJFGZKHZIZUJKHZURVCLZUKKDEVEMUQVCAKDVCANULKHZUNUTUPVBVFUMUSULKULKUJFOVFPZQVFUOVAULKULKUJFUAVGQUBUCUDRUKVCUTVDVCUTLUKUTVBSRUKUTVDUKUTIZUSUJKVHUKUSUJHUKUTSUJUEUFUKUTUGUHUITT $.  $( [30-Aug-2014] $)
    wu7 $p |- ( u e. CC -> ( u = 1 -> A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) ) ) $= ( cv c1 wceq cmul co wa cc wral wi wcel mulid2 mulid1 jca a1i ralrimiv ax-17 eqcom eqeq1d biimpi oveq1d oveq2d anbi12d ralbid mpbid ) BCZDEZUGACZFGZUIEZUIUGFGZUIEZHZAIJZKUGILUHDUIFGZUIEZUIDFGZUIEZHZAIJUOUHUTAIUIILZUTKUHVAUQUSUIMUINOPQUHUTUNAIUHARUHUQUKUSUMUHUPUJUIUHDUGUIFUHDUGEUGDSUAZUBTUHURULUIUHDUGUIFVBUCTUDUEUFP $. $( [30-Aug-2014] $)
    wu6 $p |- ( ( T. /\ 1 e. C /\ u e. CC ) -> ( A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) <-> u = 1 ) ) $= ( wtru c1 wcel cv cc w3a cmul co wceq wa wral wb simp3 wu8 wu7 impbid syl ) DECFZBGZHFZIUCUBAGZJKUDLUDUBJKUDLMAHNZUBELZODUAUCPUCUEUFABQABRST $.  $( [30-Aug-2014] $)
    wu5 $p |- ( iota_ u e. CC A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) ) = 1 $= ( wtru c1 cc wcel wa cv cmul co wceq wral crio tru ax-1cn pm3.2i wu6 riota5 ax-mp ) CDEFZGBHZAHZIJUBKUBUAIJUBKGAELZBEMDKCTNOPCUCBEDABEQRS $.  $( [30-Aug-2014] $)
    wu10 $p |- x. : ( CC X. CC ) -onto-> CC $= ( vb va cc cxp cmul wfo wf cv cfv wceq wrex wral dffo3 ax-mulopr wcel c1 wa a1i jca syl cop ax-1cn id opelxpi co mulid2 eqcomd df-ov eqtrd fveq2 eqeq2d rcla4ev rgen mpbir2an ) CCDZCEFUOCEGAHZBHZEIZJZBUOKZACLBAUOCEMNUTACUPCOZPUPUAZUOOZUPVBEIZJZQUTVAVCVEVAPCOZVAQVCVAVFVAVFVAUBRVAUCSPUPCCUDTVAUPPUPEUEZVDVAVGUPUPUFUGVGVDJVAPUPEUHRUISUSVEBVBUOUQVBJURVDUPUQVBEUJUKULTUMUN $.  $( [30-Aug-2014] $)
    wu9 $p |- ( Id ` x. ) = 1 $= ( va vb cmul cgi cfv cv co wceq wa cc wral crio c1 cvv wcel mulex crn cxp wfo ax-mp wu10 forn eqcomi gidval wu5 eqtri ) CDEZAFZBFZCGUIHUIUHCGUIHIBJKAJLZMCNOUGUJHPBACNJCQZJJJRZJCSUKJHUAULJCUBTUCUDTBAUEUF $.  $( [30-Aug-2014] $)
$}
wu2 $p |- prod_ k e. ( 1 ... 0 ) x. A = 1 $= ( c1 cc0 cfz co cmul cprd c0 cgi cfv wceq fz10OLD prodeq1 ax-mp prod0 wu9 3eqtri ) CDEFZABGHZIABGHZGJKCSILTUALMSIABGNOABGPQR $.   $( [30-Aug-2014] $)
wu3 $p |- ( n e. NN0 -> prod_ k e. ( 1 ... n ) x. 1 = 1 ) $= ? $.
wu4 $p |- E. x e. ZZ E. y e. ( NN0 ^m ( 1 ... n ) ) A. z e. ( ZZ ^m ( 1 ... 0 ) ) ( ( ( ZZ ^m ( 1 ... 0 ) ) X. { 0 } ) ` z ) = ( x x. prod_ k e. ( 1 ... 0 ) x. ( ( z ` k ) ^ ( y ` k ) ) ) $= ? $.
scalar0-is-mvzmonof0 $p |- ( ( ZZ ^m ( 1 ... 0 ) ) X. { 0 } ) e. ( MVZMonoF ` 0 ) $= ? $.
