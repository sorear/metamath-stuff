$[ set.mm $]

$( ---- MULTIVARIATE POLYNOMIALS ---- $)
$( Define multivariate polynomials and prove that they include constants and projections and are closed under addition, multiplication, and renaming of variables. Later we will also need the property that polynomial functions are computable. $)

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

$( ---- NUMBER THEORY ---- $)
$( Special Pell equations and Kummer's theorem.  Prove that certain polynomial identities are equivalent to exponential and bitwise ones. $)

$( ---- COMPUTABILITY ---- $)
$( Define Turing machines and computable functions and prove composition laws as needed. Polynomials are computable. $)

$( we're about to use this a ton, so give it a proper name $)

$c ,n 1st_n 2nd_n $.
${
    ccantor-pair $a class ,n $.
    $d x y $.

    $d a b c d e f A $.
    $d a b c d e f B $.
    $d a b c d e f C $.
    $d a b c d e f D $.

    $(
        ( ( ( A + 1 ) x. ( ( A + 1 ) + 1 ) ) / 2 ) =
        ( ( ( A + 1 ) x. ( A + ( 1 + 1 ) ) ) / 2 ) =
        ( ( ( A + 1 ) x. ( A + 2 ) ) / 2 ) =
        ( ( ( ( A + 1 ) x. A ) + ( ( A + 1 ) x. 2 ) ) / 2 ) =
        ( ( ( A x. ( A + 1 ) ) + ( ( A + 1 ) x. 2 ) ) / 2 ) =
        ( ( ( ( A + 1 ) x. A ) / 2 ) + ( ( ( A + 1 ) x. 2 ) / 2 ) ) =
        ( ( ( A + 1 ) x. A ) / 2 ) + ( A + 1 )
    $)

    $( The cantor pair.  Similar to ~ nn0opth from the core, but with the refinement of being onto. $)
    df-cantor-pair $a |- ,n = ( x e. NN0 , y e. NN0 |-> ( ( ( ( x + y ) x. ( ( x + y ) + 1 ) ) / 2 ) + x ) ) $.

    $( so we don't have to keep proving the same substitutions a billion times $)
    cantor-pair-lem13 $p |- ( A = B -> ( ( A x. ( A + 1 ) ) / 2 ) = ( ( B x. ( B + 1 ) ) / 2 ) ) $= ( wceq c1 caddc co cmul c2 cdiv id1 oveq1 oveq12d oveq1d ) ABCZAADEFZGFBBDEFZGFHINABOPGNJABDEKLM $.  $( [2-Sep-2014] $)
    cantor-pair-lem14 $p |- ( ( A = C /\ B = D ) -> ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) $= ( wceq wa caddc co c1 cmul c2 cdiv oveq12 cantor-pair-lem13 syl simpl oveq12d ) ACEZBDEZFZABGHZUAIGHJHKLHZCDGHZUCIGHJHKLHZACGTUAUCEUBUDEACBDGMUAUCNORSPQ $.  $( [2-Sep-2014] $)
    cantor-pair-value $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A ,n B ) = ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) ) $= ( va vb cn0 cv caddc co c1 cmul c2 cdiv ccantor-pair wceq weq mathbox cantor-pair-lem14 mpan2 eqid1 mpan df-cantor-pair ovex ovmpt2 ) CDABEECFZDFZGHZUFIGHJHKLHUDGHZABGHZUHIGHJHKLHZAGHZMAUEGHZUKIGHJHKLHAGHZUDANDDOUGULNDPUDUEAUEQRAANUEBNULUJNASAUEABQTCDUAUIAGUBUC $.  $( [2-Sep-2014] $)

    cantor-pair-lem3 $p |- ( A e. CC -> ( ( ( A + 1 ) x. ( ( A + 1 ) + 1 ) ) / 2 ) = ( ( ( A x. ( A + 1 ) ) / 2 ) + ( A + 1 ) ) ) $= ( cc wcel c1 caddc co cmul c2 cdiv wceq id1 ax-1cn a1i syl3anc oveq2d syl2anc oveq1d 3eqtrd ax-mulcl 2ne0 ax-addass 1p1e2apr1 idiVD eqtrd peano2cn 2cn ax-distr ax-mulcom cc0 wne wa jctir divdir divcan4 ) ABCZADEFZUPDEFZGFZHIFAUPGFZUPHGFZEFZHIFZUSHIFZUTHIFZEFZVCUPEFUOURVAHIUOURUPAHEFZGFZUPAGFZUTEFZVAUOUQVFUPGUOUQADDEFZEFZVFUOUODBCZVLUQVKJUOKZVLUOLMZVNADDUANUOVJHAEVJHJZUOVOUBUCMOUDOUOUPBCZUOHBCZVGVIJAUEZVMVQUOUFMZUPAHUGNUOVHUSUTEUOVPUOVHUSJVRVMUPAUHPQRQUOUSBCZUTBCZVQHUIUJZUKVBVEJUOUOVPVTVMVRAUPSPUOVPVQWAVRVSUPHSPUOVQWBVSTULUSUTHUMNUOVDUPVCEUOVPVQWBVDUPJVRVSWBUOTMUPHUNNOR $.  $( [1-Sep-2014] $)
    cantor-pair-lem4 $p |- ( A = 0 -> ( ( A x. ( A + 1 ) ) / 2 ) = 0 ) $= ( cc0 wceq c1 caddc co cmul c2 cdiv oveq1 cc wcel id 0cnALT a1i eqeltrd ax-1cn ax-addcl syl2anc mul02 syl eqtrd oveq1d 2cn 2ne0 div0i syl6eq ) ABCZAADEFZGFZHIFBHIFBUHUJBHIUHUJBUIGFZBABUIGJUHUIKLZUKBCUHAKLDKLZULUHABKUHMBKLUHNOPUMUHQOADRSUITUAUBUCHUDUEUFUG $.  $( [1-Sep-2014] $)
    cantor-pair-lem5 $p |- ( A e. NN0 -> ( ( A x. ( A + 1 ) ) / 2 ) e. NN0 ) $= ( vb va cv c1 caddc co cmul c2 cdiv cn0 wcel cc0 wceq id oveq1 oveq12d oveq1d eleq1d adantr weq eqid1 cantor-pair-lem4 ax-mp 0nn0 eqeltri wa cc nn0cn cantor-pair-lem3 syl simpr peano2nn0 nn0addcl syl2anc eqeltrd ex nn0ind ) BDZUSEFGZHGZIJGZKLMMEFGZHGZIJGZKLCDZVFEFGZHGZIJGZKLZVGVGEFGZHGZIJGZKLZAAEFGZHGZIJGZKLBCAUSMNZVBVEKVRVAVDIJVRUSMUTVCHVROUSMEFPQRSBCUAZVBVIKVSVAVHIJVSUSVFUTVGHVSOUSVFEFPQRSUSVGNZVBVMKVTVAVLIJVTUSVGUTVKHVTOUSVGEFPQRSUSANZVBVQKWAVAVPIJWAUSAUTVOHWAOUSAEFPQRSVEMKMMNVEMNMUBMUCUDUEUFVFKLZVJVNWBVJUGZVMVIVGFGZKWBVMWDNZVJWBVFUHLWEVFUIVFUJUKTWCVJVGKLZWDKLWBVJULWBWFVJVFUMTVIVGUNUOUPUQUR $.  $( [1-Sep-2014] $)

    $( structurally monotonic $)
    cantor-pair-lem6 $p |- ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) -> ( ( A x. ( A + 1 ) ) / 2 ) <_ ( ( B x. ( B + 1 ) ) / 2 ) ) $= ( cn0 wcel cle wbr w3a c1 caddc co cmul c2 cdiv cr cc0 wa jca syl 3syl syl2anc simp1 nn0re nn0ge0 3ad2ant2 peano2re peano2nn0 simp2 simp3 wb 1re a1i 3jca leadd1 mpbid lemul12a imp clt id1 remulcl 2re 2pos pm3.2i lediv1 syl3anc ) ACDZBCDZABEFZGZAAHIJZKJZBBHIJZKJZEFZVJLMJVLLMJEFZVHANDZOAEFZPZBNDZPZVINDZOVIEFZPZVKNDZPZPZVGVIVKEFZPZVMVHVSWDVHVQVRVHVEVQVEVFVGUAZVEVOVPAUBZAUCQRVFVEVRVGBUBZUDZQVHWBWCVHVTWAVHVEVOVTWHWIAUEZSVHVEVICDWAWHAUFVIUCSQVHVFWCVEVFVGUGZVFVRWCWJBUEZRRQQVHVGWFVEVFVGUHZVHVGWFWOVHVOVRHNDZGVGWFUIVHVOVRWPVHVEVOWHWIRWKWPVHUJUKULABHUMRUNQWEWGVMABVIVKUOUPTVHVJNDZVLNDZLNDZOLUQFZPZVMVNUIVHVEVOWQWHWIVOVOVTWQVOURWLAVIUSTSVHVFVRWRWMWJVRVRWCWRVRURWNBVKUSTSXAVHWSWTUTVAVBUKVJVLLVCVDUN $.  $( [1-Sep-2014] $)

    $(
        ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) + A ) <
        ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) + ( ( A + B ) + 1 ) ) =
        ( ( ( ( A + B ) + 1 ) x. ( ( ( A + B ) + 1 ) + 1 ) ) <=
        ( ( C + D ) x. ( ( C + D ) + 1 ) ) <=
        ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) + C )
    $)
    cantor-pair-lem9 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) e. NN0 ) $= ( cn0 wcel wa caddc co c1 cmul c2 cdiv nn0addcl cantor-pair-lem5 syl simpr simpl adantr syl2anc ex mpd ) ACDZBCDZEZABFGZUDHFGIGJKGZCDZUEAFGCDZUCUDCDUFABLUDMNUCUFUGUCUFEUFUAUGUCUFOUCUAUFUAUBPQUEALRST $.  $( [1-Sep-2014] $)

    $( separation of diagonals lemma: if two values belong to separate diagonals, they are not the same $)
    cantor-pair-lem7 $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 ) /\ ( A + B ) < ( C + D ) ) ->
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) < ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) $= ( cn0 wcel caddc co clt wbr c1 cr nn0re 3syl a1i syl2anc syl cc0 cle mpbid wa w3a cmul c2 cdiv simp1 cantor-pair-lem9 nn0addcl 1nn0 cantor-pair-lem5 simp2 simpl 1re readdcl nn0ge0 adantl wb 0re wi adantr idiVD leadd2 syl3anc wceq cc addid1 breq1d ltp1 lelttrd 3jca nn0cn ltadd2 cantor-pair-lem3 breq2d mpbird wn olci bnj1226OLD simp3 nn0ltp1le cantor-pair-lem6 eqcomd letrd ltletrd ) AEFZBEFZUAZCEFZDEFZUAZABGHZCDGHZIJZUBZWKWKKGHZUCHUDUEHZAGHZWOWOKGHUCHUDUEHZWLWLKGHUCHUDUEHZCGHZWNWGWQEFWQLFWGWJWMUFZABUGWQMNWNWOEFZWREFWRLFWNWGXBXAWGWKEFZKEFZXBABUHZXDWGUIOWKKUHPQZWOUJWRMNZWNWJWTEFWTLFWGWJWMUKZCDUGWTMNZWNWGWQWRIJZXAWGXJWQWPWOGHZIJZWGAWOIJZXLWGAWKWOWGWEALFZWEWFULAMZQWGXCWKLFZXEWKMZQZWGXPKLFZWOLFZXRXSWGUMOWKKUNPZWGARGHZWKSJZAWKSJWGRBSJZYCWFYDWEBUOUPWGRLFZBLFZXNYDYCUQYEWGUROWFYFWEBMUPWGXNUSWEXNWFXOUTVAZRBAVBVCTWGYBAWKSWEYBAVDZWFWEAVEFYHAVKAVFQUTVGTWGXCXPWKWOIJXEXQWKVHNVIWGXNXTWPLFZUBXMXLUQWGXNXTYIYGYAWGXCWPEFYIXEWKUJWPMNVJAWOWPVLQTWGWRXKWQIWGWKVEFZWRXKVDWGXCYJXEWKVKQWKVMQVNVOQWNWRWSRGHZWTXGWNWSLFZYEYKLFWNWJYLXHWJWLEFZWSEFZYLCDUHZWLUJZWSMNZQWNYEYEWNVPURVQVRWSRUNPXIWNWRWSSJZWRYKSJWNXBYMWOWLSJZYRXFWNWJYMXHYOQZWNWMYSWGWJWMVSWNXCYMWMYSUQWNWGXCXAXEQYTWKWLVTPTWOWLWAVCWNWSYKWRSWNYKWSWNWSVEFZYKWSVDWNYMYNUUAYTYPWSVKNWSVFQWBVNTWNRCSJZYKWTSJZWNWJWHUUBXHWHWIULZCUONWNYECLFZYLUBZUUBUUCUQWNWJUUFXHWJYEUUEYLYEWJUROWJWHUUEUUDCMQYQVJQRCWSVBQTWCWD $.  $( [1-Sep-2014] $)

    $( first, use the trichotomy law to show that they must be in the same diagonal, because if > or < the values would be different.  then get the result by cancellation $)
    cantor-pair-lem8 $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 ) /\
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) -> ( A = C /\ B = D ) ) $= ( cn0 wcel wa caddc co wceq clt wbr wn 3syl mpbid adantr simpr syl3anc cc nn0cn c1 cmul c2 cdiv w3a cr simp1 cantor-pair-lem9 nn0re ltnr syl simp3 breq2d notbid simp2 cantor-pair-lem7 ex mtod breq1d jca wb nn0addcl lttri3 syl2anc mpbird eqimss2 eqimss eqssd adantl oveq1d oveq12d eqtrd cantor-pair-lem5 simpl addcan eqcom biimpi oveq1 mpdan ) AEFZBEFZGZCEFZDEFZGZABHIZWFUAHIZUBIZUCUDIZAHIZCDHIZWKUAHIZUBIZUCUDIZCHIZJZUEZWFWKJZACJZBDJZGZWQWRWFWKKLZMZWKWFKLZMZGZWQXCXEWQXBWJWOKLZWQWJWJKLZMZXGMWQWJUFFZXIWQWBWJEFXJWBWEWPUGZABUHWJUINWJUJUKZWQXHXGWQWJWOWJKWBWEWPULZUMUNOWQXBXGWQXBGWBWEXBXGWQWBXBXKPWQWEXBWBWEWPUOZPWQXBQABCDUPRUQURWQXDWOWJKLZWQXIXOMXLWQXHXOWQWJWOWJKXMUSUNOWQXDXOWQXDGWEWBXDXOWQWEXDXNPWQWBXDXKPWQXDQCDABUPRUQURUTWQWFUFFZWKUFFZWRXFVAWQWBWFEFZXPXKABVBZWFUINWQWEWKEFXQXNCDVBWKUINWFWKVCVDVEWQWRGZWSXAXTWJWICHIZJZWSXTWJWOYAWQWPWRXMPXTWNWICHXTWMWHUCUDXTWKWFWLWGUBWRWKWFJWQWRWKWFWKWFVFWFWKVGVHVIZXTWKWFUAHYCVJVKVJVJVLXTWISFZASFZCSFZYBWSVAXTWBXRYDWQWBWRXKPXSXRWIEFYDWFVMWITUKNWQYEWRWQWBVTYEXKVTWAVNATNPZWQYFWRWQWEWCYFXNWCWDVNCTNPWIACVOROXTWSGZWSWTXTWSQYHWFADHIZJZWTYHWFWKYIXTWRWSWQWRQPWSWKYIJZXTWSCAJZYKWSYLACVPVQCADHVRUKVIVLYHYEBSFZDSFZYJWTVAXTYEWSYGPXTYMWSWQYMWRWQWBWAYMXKVTWAQBTNPPXTYNWSWQYNWRWQWEWDYNXNWCWDQDTNPPABDVOROUTVSVS $.  $( [1-Sep-2014] $)

    cantor-pair-lem10 $p |- E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = 0 $= ( cc0 cn0 wcel caddc co c1 cmul c2 cdiv wceq cv wrex 0nn0 cc ax-mp oveq1d oveq12d eqeq1d nn0addcli cantor-pair-lem5 nn0cn syl addid1i 00id cantor-pair-lem4 eqtri oveq1 id oveq2 rcla42ev mp3an ) CDEZUNCCFGZUOHFGZIGZJKGZCFGZCLZAMZBMZFGZVCHFGZIGZJKGZVAFGZCLZBDNADNOOUSURCURUODEZURPEZCCOOUAVIURDEVJUOUBURUCUDQUEUOCLURCLUFUOUGQUHVHUTCVBFGZVKHFGZIGZJKGZCFGZCLABCCDDVACLZVGVOCVPVFVNVACFVPVEVMJKVPVCVKVDVLIVACVBFUIZVPVCVKHFVQRSRVPUJSTVBCLZVOUSCVRVNURCFVRVMUQJKVRVKUOVLUPIVBCCFUKZVRVKUOHFVSRSRRTULUM $.  $( [1-Sep-2014] $)
    cantor-pair-lem11 $p |- ( A e. NN0 ->
        ( E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = A ->
            E. c e. NN0 E. d e. NN0 ( ( ( ( c + d ) x. ( ( c + d ) + 1 ) ) / 2 ) + c ) = ( A + 1 ) ) ) $= ( cn0 wcel caddc co c1 cmul c2 cdiv wceq cc0 a1i adantr cc syl oveq1d cv wrex wa wi w3a 0nn0 simp3 simpl id 1nn0 nn0addcl syl2anc 3ad2ant3 cantor-pair-lem5 nn0cn addid1 simpl2 oveq2d 0cnALT addcom ax-1cn ax-addass syl3anc 3eqtrd 0cn oveq12d eqeq1d cantor-pair-lem3 3syl mpbid adantl eqcomd eqid1 simp2 eqtrd mpdan simpr oveq1 oveq2 rcla42ev 3exp1 wn cmin cn wo elnn0 biimpi orcomd ord mpd nnm1nn0 id1 subcl npcan weq eqid pm2.61d rexlimdvv ) AFGZBUAZCUAZHIZXBJHIZKIZLMIZWTHIZANZDUAZEUAZHIZXJJHIZKIZLMIZXHHIZAJHIZNZEFUBDFUBZBCFFWSXAONZWTFGZXAFGZUCZXGXQUDUDWSXRYAXGXQWSXRYAUEZXGUCZOFGZWTJHIZFGZOYEHIZYGJHIZKIZLMIZOHIZXONZXQYDYCUFPYBYFXGYBYAXSYFWSXRYAUGXSXTUHZXSXSJFGZYFXSUIYNXSUJPWTJUKULZVIQYCYKXCXCJHIZKIZLMIZXEXCHIZXOYCYROHIZYRNZYKYRNYCYRFGZYRRGUUAYCXCFGZUUBYCXBFGZYNUUCYBUUDXGYAWSUUDXRWTXAUKZUMZQZYNYCUJPXBJUKULXCUNSYRUOYRUPVIYCYTYKYRYCYRYJOHYCYQYILMYCXCYGYPYHKYCXCWTOHIZJHIZOWTHIZJHIZYGYCXBUUHJHYCXAOWTHWSXRYAXGUQURTZYCUUHUUJJHYCWTRGZORGZUUHUUJNZYBUUMXGYAWSUUMXRXSUUMXTWTUOQZUMZQZUUNYCUSPZWTOUTZULTYCUUNUUMJRGZUUKYGNZUUSUURUVAYCVAPZOWTJVBZVCVDYCXCYGJHYCXCUUIUUKYGUULYCUUHUUJJHYCUUMUUNUUOUURUUNYCVEPZUUTULTYCUUNUUMUVAUVBUVEUURUVCUVDVCVDTVFTTVGVJYCXBRGZYRYSNYCUUDUVFUUGXBUOZSXBVHSYCYSXFJHIZXOYBYSUVHNZXGYBUUDUVIUUFYBUUDUCZYSXEXBHIZJHIZUVLUVHUVJXERGZUVFUVAYSUVLNUVJXEFGZUVMUUDUVNYBXBUNZVKXEUOZSUUDUVFYBUVGVKUVAUVJVAPUVMUVFUVAUEUVLYSXEXBJVBVLVCUVLUVLNUVJUVLVMPUVJUVKXFJHUVJXBWTXEHUVJXBUUHWTUVJXAOWTHYBXRUUDWSXRYAVNQURUVJUUMUUHWTNYBUUMUUDUUQQWTUPSVOURTVDVPQYCXFAJHYBXGVQTVOVDXPYLOXIHIZUVQJHIZKIZLMIZOHIZXONDEOYEFFXHONZXNUWAXOUWBXMUVTXHOHUWBXLUVSLMUWBXJUVQXKUVRKXHOXIHVRZUWBXJUVQJHUWCTVFTUWBUIVFVGXIYENZUWAYKXOUWDUVTYJOHUWDUVSYILMUWDUVQYGUVRYHKXIYEOHVSZUWDUVQYGJHUWETVFTTVGVTVCWAWSXRWBZYAXGXQWSUWFYAUEZXGUCZYFXAJWCIZFGZYEUWIHIZUWKJHIZKIZLMIZYEHIZXONZXQUWGYFXGUWGYAXSYFWSUWFYAUGZYMYOVIQUWGUWJXGUWGXAWDGZUWJUWGUWFUWRWSUWFYAVNUWGXRUWRUWGUWRXRYAWSUWRXRWEZUWFXTUWSXSXTUWSXAWFWGVKUMWHWIWJXAWKSQUWHUWKXBNZUWPUWGUWTXGYAWSUWTUWFYAUWKWTJUWIHIZHIZXBXBYAUUMUVAUWIRGZUWKUXBNUUPUVAYAVAPZXTUXCXSXTXARGZUXCXAUOZUXEUXEUVAUXCUXEWLZUVAUXEVAPZXAJWMULZSVKWTJUWIVBVCYAUXAXAWTHYAUXEUXAXANXTUXEXSUXFVKUXEUXAUWIJHIZXAXAUXEUVAUXCUXAUXJNUXHUXIJUWIUTULUXEUXEUVAUXJXANUXGUXHXAJWNULCCWOUXEXAWPPVDSURXBXBNYAXBWPPVDUMQUWHUWTUCZUWOXEYEHIZXOUXKUWNXEYEHUXKUWMXDLMUXKUWKXBUWLXCKUWHUWTVQZUXKUWKXBJHUXMTVFTTUWHUXLXONUWTUWHUXLUVHXOUWHYAUXLUVHNZUWGYAXGUWQQYAUVMUUMUVAUXNYAUUDUVNUVMUUEUVOUVPVIUUPUXDUVMUUMUVAUEUVHUXLXEWTJVBVLVCSUWHXFAJHUWGXGVQTVOQVOVPXPUWPYEXIHIZUXOJHIZKIZLMIZYEHIZXONDEYEUWIFFXHYENZXNUXSXOUXTXMUXRXHYEHUXTXLUXQLMUXTXJUXOXKUXPKXHYEXIHVRZUXTXJUXOJHUYATVFTUXTUIVFVGXIUWINZUXSUWOXOUYBUXRUWNYEHUYBUXQUWMLMUYBUXOUWKUXPUWLKXIUWIYEHVSZUYBUXOUWKJHUYCTVFTTVGVTVCWAWQWR $.  $( [1-Sep-2014] $)
    cantor-pair-lem12 $p |- ( A e. NN0 -> E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = A ) $= ( vc vd cv caddc co c1 cmul c2 cdiv wceq cn0 wrex eqeq2 2rexbidv weq oveq1d oveq12d ve vf cc0 cantor-pair-lem10 wcel cantor-pair-lem11 oveq1 id eqeq1d oveq2 eqid a1i cbvrex2v biimpi syl6 nn0ind ) BFZCFZGHZUSIGHZJHZKLHZUQGHZUAFZMZCNOBNOVCUCMZCNOBNOVCUBFZMZCNOBNOZVCVGIGHZMZCNOBNOZVCAMZCNOBNOUAUBAVDUCMVEVFBCNNVDUCVCPQUAUBRVEVHBCNNVDVGVCPQVDVJMVEVKBCNNVDVJVCPQVDAMVEVMBCNNVDAVCPQBCUDVGNUEVIDFZEFZGHZVPIGHZJHZKLHZVNGHZVJMZENODNOZVLVGBCDEUFWBVLWAVKUQVOGHZWCIGHZJHZKLHZUQGHZVJMDEBCNNDBRZVTWGVJWHVSWFVNUQGWHVRWEKLWHVPWCVQWDJVNUQVOGUGZWHVPWCIGWISTSWHUHTUIECRZWGVCVJWJWFVBUQUQGWJWEVAKLWJWCUSWDUTJVOURUQGUJZWJWCUSIGWKSTSBBRWJUQUKULTUIUMUNUOUP $.  $( [1-Sep-2014] $)

    cantor-pair-map $p |- ,n : ( NN0 X. NN0 ) --> NN0 $= ( va vb cv caddc co c1 cmul c2 cdiv cn0 wcel wral cxp ccantor-pair wf cantor-pair-lem9 rgen2 df-cantor-pair fmpt2 mpbi ) ACZBCZDEZUCFDEGEHIEUADEZJKZBJLAJLJJMJNOUEABJJUAUBPQABJJUDJNABRST $.

    cantor-pair     $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 ) /\ ( A ,n B ) = ( C ,n D ) ) -> ( A = C /\ B = D ) ) $= ( va vb vc cn0 wcel ccantor-pair co wceq caddc c1 cmul c2 cdiv cv oveq1d oveq12d vd wa w3a simp1 simp2 oveq1 id oveq2 df-cantor-pair ovex ovmpt2 3ad2ant1 eqcomd simp3 3ad2ant2 3eqtrd cantor-pair-lem8 syl3anc ) AHIBHIUBZCHIDHIUBZABJKZCDJKZLZUCZUSUTABMKZVENMKZOKZPQKZAMKZCDMKZVJNMKZOKZPQKZCMKZLACLBDLUBUSUTVCUDUSUTVCUEVDVIVAVBVNVDVAVIUSUTVAVILVCEFABHHERZFRZMKZVQNMKZOKZPQKZVOMKVIJAVPMKZWANMKZOKZPQKZAMKVOALZVTWDVOAMWEVSWCPQWEVQWAVRWBOVOAVPMUFZWEVQWANMWFSTSWEUGTVPBLZWDVHAMWGWCVGPQWGWAVEWBVFOVPBAMUHZWGWAVENMWHSTSSEFUIVHAMUJUKULUMUSUTVCUNUTUSVBVNLVCGUACDHHGRZUARZMKZWKNMKZOKZPQKZWIMKVNJCWJMKZWONMKZOKZPQKZCMKWICLZWNWRWICMWSWMWQPQWSWKWOWLWPOWICWJMUFZWSWKWONMWTSTSWSUGTWJDLZWRVMCMXAWQVLPQXAWOVJWPVKOWJDCMUHZXAWOVJNMXBSTSSGUAUIVMCMUJUKUOUPABCDUQUR $.  $( [1-Sep-2014] $)

    cantor-pair-1   $p |- ,n : ( NN0 X. NN0 ) -1-1-> NN0 $= ( va vb cn0 ccantor-pair cv cfv wceq wcel wa caddc co c1 cmul c2 cdiv biimpi simpr oveq1d oveq12d eqtrd ve vf vc vd cxp wf1 wf weq wral dff13 cantor-pair-map c1st c2nd cop cvv simpll elxp7 3syl simplr elxp6 ad2antrr ad2antlr w3a simpl fveq2d df-ov eqcomi a1i oveq1 wi id oveq2 df-cantor-pair ovex ovmpt2 adantl 3ad2ant1 eqcomd simp3 3ad2ant2 3eqtrd syl3anc cantor-pair-lem8 1st2nd2 opeq12d simp2 3eqtr4d ex rgen2 mpbir2an ) CCUEZCDUFWKCDUGAEZDFZBEZDFZGZABUHZVJZBWKUIAWKUIABWKCDUJUKWRABWKWKWLWKHZWNWKHZIZWPWQXAWPIZWLULFZWNULFZGZWLUMFZWNUMFZGZIZWLXCXFUNZGZWNXDXGUNZGZWQXBXCCHXFCHIZXDCHXGCHIZXCXFJKZXPLJKZMKZNOKZXCJKZXDXGJKZYALJKZMKZNOKZXDJKZGZXIXBWSWLUOUOUEZHZXNIZXNWSWTWPUPWSYIWLCCUQPYHXNQURXBWTWNYGHZXOIZXOWSWTWPUSWTYKWNCCUQPYJXOQURXBXKXNIZXMXOIZWPYFWSYLWTWPWSYLWLCCUTPVAWTYMWSWPWTYMWNCCUTPVBXAWPQYLYMWPVCZXTWMWOYEYNWMXTYLYMWMXTGWPYLWMXJDFZXTYLWLXJDXKXNVDVEXNYOXTGXKXNYOXCXFDKZXTYOYPGXNYPYOXCXFDVFVGVHUAUBXCXFCCUAEZUBEZJKZYSLJKZMKZNOKZYQJKXTDXCYRJKZUUCLJKZMKZNOKZXCJKYQXCGZUUBUUFYQXCJUUGUUAUUENOUUGYSUUCYTUUDMYQXCYRJVIZUUGYSUUCLJUUHRSRUUGVKSYRXFGZUUFXSXCJUUIUUEXRNOUUIUUCXPUUDXQMYRXFXCJVLZUUIUUCXPLJUUJRSRRUAUBVMXSXCJVNVOTVPTVQVRYLYMWPVSYMYLWOYEGWPYMWOXLDFZYEYMWNXLDXMXOVDVEXOUUKYEGXMXOUUKXDXGDKZYEUUKUULGXOUULUUKXDXGDVFVGVHUCUDXDXGCCUCEZUDEZJKZUUOLJKZMKZNOKZUUMJKYEDXDUUNJKZUUSLJKZMKZNOKZXDJKUUMXDGZUURUVBUUMXDJUVCUUQUVANOUVCUUOUUSUUPUUTMUUMXDUUNJVIZUVCUUOUUSLJUVDRSRUVCVKSUUNXGGZUVBYDXDJUVEUVAYCNOUVEUUSYAUUTYBMUUNXGXDJVLZUVEUUSYALJUVFRSRRUCUDVMYDXDJVNVOTVPTVTWAWBXCXFXDXGWCWBWSXKWTWPWLCCWDVAWTXMWSWPWNCCWDVBXIXKXMVCXJXLWLWNXIXKXJXLGXMXIXCXDXFXGXEXHVDXEXHQWEVQXIXKXMWFXIXKXMVSWGWBWHWIWJ $.  $( [1-Sep-2014] $)

    cantor-pair-o   $p |- ,n : ( NN0 X. NN0 ) -onto-> NN0 $= ( vc vd va vb ve vf cn0 ccantor-pair cv wceq wrex wcel caddc co c1 cmul c2 cdiv wa oveq1d cxp wfo wf cfv wral dffo3 cantor-pair-map cantor-pair-lem12 cop opelxpi adantl adantr id eqcomd cvv simplrl simplrr a1i weq oveq1 oveq12d oveq2 df-cantor-pair ovmpt2g syl3anc ovex df-ov 3eqtrd fveq2 eqeq2d rcla4ev syl2anc ex rexlimdvva mpd rgen mpbir2an ) GGUAZGHUBVRGHUCAIZBIZHUDZJZBVRKZAGUEBAVRGHUFUGWCAGVSGLZCIZDIZMNZWGOMNZPNZQRNZWEMNZVSJZDGKCGKWCVSCDUHWDWLWCCDGGWDWEGLZWFGLZSZSZWLWCWPWLSZWEWFUIZVRLZVSWRHUDZJZWCWPWSWLWOWSWDWEWFGGUJUKULWQVSWKWEWFHNZWTWLVSWKJWPWLWKVSWLUMUNUKWQXBWKWQWMWNWKUOLZXBWKJWDWMWNWLUPWDWMWNWLUQXCWQWJWEMVFUREFWEWFGGEIZFIZMNZXFOMNZPNZQRNZXDMNWKHWEXEMNZXJOMNZPNZQRNZWEMNUOECUSZXIXMXDWEMXNXHXLQRXNXFXJXGXKPXDWEXEMUTZXNXFXJOMXOTVATXNUMVAFDUSZXMWJWEMXPXLWIQRXPXJWGXKWHPXEWFWEMVBZXPXJWGOMXQTVATTEFVCVDVEUNXBWTJWQWEWFHVGURVHWBXABWRVRVTWRJWAWTVSVTWRHVIVJVKVLVMVNVOVPVQ $.  $( [1-Sep-2014] $)

    cantor-pair-1o  $p |- ,n : ( NN0 X. NN0 ) -1-1-onto-> NN0 $= ( cn0 cxp ccantor-pair wf1o wf1 wfo df-f1o cantor-pair-1 cantor-pair-o mpbir2an ) AABZACDKACEKACFKACGHIJ $.  $( [1-Sep-2014] $)

    cantor-pair-le1 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> A <_ ( A ,n B ) ) $= ( va vb cn0 wcel wa caddc co c1 cmul c2 cdiv cle cc0 wceq syl adantr cr oveq1d ccantor-pair cc nn0cn addid2 w3a wbr nn0addcl cantor-pair-lem5 nn0re 0reALT a1i simpr 3jca nn0ge0 jca syl2anc leadd1 biimpa eqbrtrrd cv oveq1 oveq12d id oveq2 df-cantor-pair ovex ovmpt2 breqtrrd ) AEFZBEFZGZAABHIZVLJHIZKIZLMIZAHIZABUAINVKOAHIZAVPNVIVQAPZVJVIAUBFVRAUCAUDQRVKOSFZVOSFZASFZUEZOVONUFZGZVQVPNUFZVKVOEFZWAWDVKVLEFWFABUGVLUHQVIWAVJAUIRWFWAGZWBWCWGVSVTWAVSWGUJUKWFVTWAVOUIRWFWAULUMWFWCWAVOUNRUOUPWBWCWEOVOAUQURQUSCDABEECUTZDUTZHIZWJJHIZKIZLMIZWHHIVPUAAWIHIZWNJHIZKIZLMIZAHIWHAPZWMWQWHAHWRWLWPLMWRWJWNWKWOKWHAWIHVAZWRWJWNJHWSTVBTWRVCVBWIBPZWQVOAHWTWPVNLMWTWNVLWOVMKWIBAHVDZWTWNVLJHXATVBTTCDVEVOAHVFVGVH $.  $( [1-Sep-2014] $)


    cantor-pair-fixpoint $p |- ( 0 ,n 0 ) = 0 $= ( cc0 ccantor-pair co caddc c1 cmul c2 cdiv cn0 wcel wceq 0nn0 cantor-pair-value mp2an 00id cantor-pair-lem4 oveq1d ax-mp eqtri ) AABCZAADCZUAEDCFCGHCZADCZAAIJZUDTUCKLLAAMNUCUAAUAAKZUCUAKOUEUBAADUAPQROSS $.  $( [2-Sep-2014] $)

    cantor-pair-le2 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> B <_ ( A ,n B ) ) $= ? $.
$}

$( loosely inspired by some lecture notes I found by Lou van den Dries $)
$c RecZer RecSuc RecSub RecSea RecPrj RecPrc RecParF RecArity RecParFa RecTotF RecTotFa RecArithPrimitiveStep RecArithGeneralStep RecArithPrimitiveL RecArithPrimitive RecArithGeneralL RecArithGeneral RecPrimitive RecGeneral RecPreList $.
${
    creczer $a class RecZer $.
    crecsuc $a class RecSuc $.
    crecprj $a class RecPrj $.
    crecsub $a class RecSub $.
    crecsea $a class RecSea $.
    crecprc $a class RecPrc $.
    crecparf $a class RecParF $.
    crecarity $a class RecArity $.
    crecparfa $a class RecParFa $.
    crectotf $a class RecTotF $.
    crectotfa $a class RecTotFa $.
    crecprelist $a class RecPreList $.
    crecarithprimitivestep $a class RecArithPrimitiveStep $.
    crecarithprimitivel $a class RecArithPrimitiveL $.
    crecarithprimitive $a class RecArithPrimitive $.
    crecprimitive $a class RecPrimitive $.
    crecarithgeneralstep $a class RecArithGeneralStep $.
    crecarithgenerall $a class RecArithGeneralL $.
    crecarithgeneral $a class RecArithGeneral $.
    crecgeneral $a class RecGeneral $.

    $d x y z f g h w a b c i j k $.

    $( -- unified treatment of partial/total functions for recursion theory -- $)

    $( Set of partial functions from NN^x -> NN, not necessarily recursive.  Set theoretically these are total functions, in order to avoid a pathology where nowhere-defined functions can have multiple arities at the same time. $)
    df-recparfa $a |- RecParFa = ( x e. NN |-> ( ( NN0 u. { ( Undef ` NN0 ) } ) ^m ( NN0 ^m ( 1 ... x ) ) ) ) $.

    $( All partial functions, regardless of arity $)
    df-recparf $a |- RecParF = U. ran RecParFa $.

    $( Arity of a partial function $)
    df-recarity $a |- RecArity = ( f e. RecParF |-> ( iota_ x e. NN f e. ( RecParFa ` x ) ) ) $.

    $( Total functions, a subset of partial functions $)
    df-rectotfa $a |- RecTotFa = ( x e. NN |-> ( NN0 ^m ( NN0 ^m ( 1 ... x ) ) ) ) $.
    df-rectotf $a |- RecTotF = U. ran RecTotFa $.
    $( we can use the same arity $)

    $( TODO: define RecPreList $)

    $( -- recursive function builders -- $)

    $( Zero recursive function $)
    df-reczer $a |- RecZer = ( x e. ( NN0 ^m ( 1 ... 0 ) ) |-> 0 ) $.
    $( Successor $)
    df-recsuc $a |- RecSuc = ( x e. ( NN0 ^m ( 1 ... 1 ) ) |-> ( ( x ` 1 ) + 1 ) ) $.
    $( Projector family $)
    df-recprj $a |- RecPrj = ( x e. NN , y e. NN |-> ( z e. ( NN0 ^m ( 1 ... y ) ) |-> if ( x <_ y , ( z ` x ) , 0 ) ) ) $.
    $( Substitution $)
    df-recsub $a |- RecSub =
        ( x e. NN , y e. NN |->
            ( f e. ( RecParFa ` x ) , g e. ( ( RecParFa ` y ) ^m ( 1 ... x ) ) |->
                ( h e. ( NN ^m ( 1 ... y ) ) |->
                    if (
                        E. z e. ( 1 ... x ) ( ( g ` z ) ` h ) = ( Undef ` NN0 ) ,
                        ( Undef ` NN0 ) ,
                        ( f ` ( w e. ( 1 ... x ) |-> ( ( g ` w ) ` h ) ) )
                    )
                )
            )
        )
    $.

    $( Primitive recursion $)
    df-recprc $a |- RecPrc = ( x e. NN |->
        ( g e. ( RecParFa ` x ) , h e. ( RecParFa ` ( x + 1 ) ) |->
            ( y e. ( 1 ... ( x + 1 ) ) |->
                ( seq 0 (
                    ( w e. ( NN0 u. { ( Undef ` NN0 ) } ) , a e. ( NN0 u. { ( Undef ` NN0 ) } ) |->
                        if ( w = ( Undef ` NN0 ) , ( Undef ` NN0 ) ,
                            ( h ` ( ( y |` ( 1 ... x ) ) u. { <. ( x + 1 ) , w >. } ) )
                        )
                    ) ,
                    ( NN0 X. { g ` ( y |` ( 1 ... x ) ) } )
                ) ` ( y ` ( x + 1 ) ) )
            )
        )
    ) $.

    $( Unbounded search / general recursion.  Here originates Undef. $)
    df-recsea $a |- RecSea = ( x e. NN |->
        ( f e. ( RecParFa ` ( x + 1 ) ) |->
            ( y e. ( 1 ... x ) |->
                ( iota_ z e. NN0 (
                    ( f ` ( y u. { <. ( x + 1 ) , z >. } ) ) = 0 /\
                    A. w e. NN0 ( w < z -> ( f ` ( y u. { <. ( x + 1 ) , z >. } ) ) e. ( NN0 \ { 0 } ) )
                ) )
            )
        )
    ) $.

    $( -- let's define the arithmetization predicate and the set of general recursive functions at the same time, I think this will save work -- $)

    $( naming a step of the construction, do not use except to prove properties on RecArithPrimitiveL $)
    df-recarithprimitivestep $a |- RecArithPrimitiveStep = ( f e. ~P ( NN0 X. RecParF ) |-> { <. x , g >. |
        (
            ( ( x = ( 1 ,n 0 ) /\ g = RecZer ) \/
                ( x = ( 1 ,n 1 ) /\ g = RecSuc ) ) \/
            (
                E. i e. NN E. j e. NN ( x = ( 2 ,n ( i ,n j ) ) /\ i <_ j /\ g = ( i RecPrj j ) ) \/
                E. i e. NN E. j e. NN E. a e. ( RecParFa ` i ) E. b e. ( ( RecParFa ` j ) ^m ( 1 ... i ) )
                    E. c e. NN0 E. d e. NN0 E. e e. ( NN0 ^m ( 1 ... i ) )
                        ( ( c f a /\ A. l e. ( 1 ... i ) ( e ` l ) f ( b ` l ) ) /\
                            ( x = ( 3 ,n ( i ,n ( c ,n d ) ) ) /\ d = ( RecPreList ` e ) /\  g = ( a ( i RecSub j ) b ) ) ) \/
                E. i e. NN E. j e. NN0 E. k e. NN0 E. a e. ( RecParFa ` i ) E. b e. ( RecParFa ` ( i + 1 ) )
                    ( ( j f a /\ k f b ) /\ ( x = ( 4 ,n ( j ,n k ) ) /\ g = ( a ( RecPrc ` i ) b ) ) )
            )
        )
    } ) $.

    df-recarithgeneralstep $a |- RecArithGeneralStep ( f e. ~P ( NN0 X. RecParF ) |-> { <. x , g >. |
        x ( RecArithPrimitiveStep ` f ) g \/
        E. i e. NN E. j e. NN0 E. a e. ( RecParFa ` ( i + 1 ) )
            ( j f a /\ x = ( 5 ,n j ) /\ g = ( ( RecSea ` i ) ` a ) )
    } ) $.

    $( Primitive recursion - levelled version, avoid using $)
    df-recarithprimitivel $a |- RecArithPrimitiveL = rec ( RecArithPrimitiveStep , (/) ) $.
    df-recarithgenerall $a |- RecArithGeneralL = rec ( RecArithGeneralStep , (/) ) $.
    df-recarithprimitive $a |- RecArithPrimitive = ( RecArithPrimitiveL ` om ) $.
    df-recarithgeneral $a |- RecArithGeneral = ( RecArithGeneralL ` om ) $.
    df-recprimitive $a |- RecPrimitive = ran RecArithPrimitive $.
    df-recgeneral $a |- RecGeneral = ran RecArithGeneral $.
$}

${
    $d a b c d e f g $.

    totfa-is-parfa $p |- ( A e. NN -> ( RecTotFa ` A ) C_ ( RecParFa ` A ) ) $= ? $.
    totf-is-parf $p |- RecTotF C_ RecParF $= ? $.
    parfa-disjoint $p |- ( ( ( A e. NN /\ B e. NN ) /\ ( C e. ( RecParFa ` A ) /\ C e. ( RecParFa ` B ) ) ) -> A = B ) $= ? $.
    arity-defined $p |- ( A e. RecParF -> ( RecArity ` A ) e. NN ) $= ? $.
    arity-fun $p |- RecArity : RecParF --> NN $= ? $.
    arity-df2 $p |- ( A e. NN -> ( B e. ( RecParFa ` A ) <-> ( B e. RecParF /\ ( RecArity ` B ) = A ) ) ) $= ? $.
    arity-dftot $p |- ( A e. NN -> ( B e. ( RecTotFa ` A ) <-> ( B e. RecTotF /\ ( RecArity ` B ) = A ) ) ) $= ? $.
$}

${
    $d a b c d e f g $.

    zer-totfa $p |- RecZer e. ( RecTotFa ` 0 ) $= ? $.
    suc-totfa $p |- RecSuc e. ( RecTotFa ` 1 ) $= ? $.
    prj-totfa $p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) e. ( RecTotFa ` B ) ) $= ? $.
    sub-totfa $p |- ( ( ( A e. NN /\ B e. NN ) /\ ( C e. ( RecTotFa ` A ) /\ D e. ( ( RecTotFa ` B ) ^m ( 1 ... A ) ) ) ) -> ( C ( A RecSub B ) D ) e. ( RecTotFa ` B ) ) $= ? $.
    sub-parfa $p |- ( ( ( A e. NN /\ B e. NN ) /\ ( C e. ( RecParFa ` A ) /\ D e. ( ( RecParFa ` B ) ^m ( 1 ... A ) ) ) ) -> ( C ( A RecSub B ) D ) e. ( RecParFa ` B ) ) $= ? $.
    prc-totfa $p |- ( ( A e. NN /\ B e. ( RecTotFa ` A ) /\ C e. ( RecTotFa ` ( A + 1 ) ) ) -> ( B ( RecPrc ` A ) C ) e. ( RecTotFa ` ( A + 1 ) ) ) $= ? $.
    prc-parfa $p |- ( ( A e. NN /\ B e. ( RecParFa ` A ) /\ C e. ( RecParFa ` ( A + 1 ) ) ) -> ( B ( RecPrc ` A ) C ) e. ( RecParFa ` ( A + 1 ) ) ) $= ? $.
    sea-parfa $p |- ( ( A e. NN /\ B e. ( RecParFa ` ( A + 1 ) ) ) -> ( ( RecSea ` A ) ` B ) e. ( RecParFa ` A ) ) $= ? $.
$}

${
    $d a b c d e f g $.

    $( we probably need to go finer grained than this $)

    prim-is-gen-lem0 $p |- ( ( B C_ ( NN0 X. RecParF ) /\ A C_ B ) -> ( RecArithPrimitiveStep ` A ) C_ ( RecArithPrimitiveStep ` B ) ) $= ? $.
    prim-is-gen-lem1 $p |- ( ( B C_ ( NN0 X. RecParF ) /\ A C_ B ) -> ( RecArithGeneralStep ` A ) C_ ( RecArithGeneralStep ` B ) ) $= ? $.
    prim-is-gen-lem2 $p |- ( A C_ ( NN0 X. RecParF ) -> ( RecArithPrimitiveStep ` A ) C_ ( RecArithGeneralStep ` A ) ) $= ? $.
    prim-is-gen-lem3 $p |- ( X e. On -> ( RecArithPrimitiveL ` X ) C_ ( RecArithGeneralL ` X ) ) $= ? $.
    prim-is-gen-arith $p |- RecArithPrimitive C_ RecArithGeneral $= ? $.
    prim-is-gen $p |- RecPrimitive C_ RecGeneral $= ? $.

    $( not super sure how to prove these $)

    gen-arith-isfun $p |- Fun RecArithGeneral $= ? $.
    gen-arith-dom $p |- dom RecArithGeneral C_ NN $= ? $.
    gen-are-parf $p |- RecGeneral C_ RecParF $= ? $.

    $( easy consequences of the above, except for prim-are-totf $)
    prim-arith-isfun $p |- Fun RecArithPrimitive $= ? $.
    prim-arith-dom $p |- dom RecArithPrimitive C_ NN $= ? $.
    prim-are-totf $p |- RecPrimitive C_ RecTotF $= ? $.

    $( nonconstructive cardinality proof.  we will see the explicit diagonalization construction later $)
    ex-nongen-totf-card-lem0 $p |- RecGeneral ~< NN $= ? $.
    ex-nongen-totf-card-lem1 $p |- RecParF ~~ ~P NN $= ? $.
    ex-nongen-totf-card $p |- RecGeneral C. RecParF $= ? $.
$}

${
    $( construction and induction principles $)

    zer-arith-prim $p |- <. ( 1 ,n 0 ) , RecZer >. e. RecPrimitive $= ? $.
    suc-arith-prim $p |- <. ( 1 ,n 1 ) , RecSuc >. e. RecPrimitive $= ? $.
    prj-arith-prim $p |- ( ( A e. NN /\ B e. NN /\ A <_ B ) -> <. ( 2 ,n ( A ,n B ) ) , ( A RecPrj B ) >. e. RecPrimitive ) $= ? $.

    zer-prim $p |- RecZer e. RecPrimitive $= ? $.
    suc-prim $p |- RecSuc e. RecPrimitive $= ? $.

    prim-en-nn $p |- RecPrimitive ~~ NN $= ? $.
    gen-en-nn $p |- RecGeneral ~~ NN $= ? $.

    $( We may not need a full induction schema; coinduction + Goedel implies that ordinary induction on NN0 can be lifted to induction here $)
$}

$( ---- HALTING ---- $)
$( Prove the existance of a Universal Turing Machine (i.o.w. the Turing evaluation function is a partial computable function) and formalize the existance of semidecidable predicates that are not decidable. $)

$( doing this by recursion theory now.
   define [] = 0, (x:y) = ( x ,n y ) + 1
   define a primitive-recursive step function on stacks of frames:
   step ( [_,[1,0]] : (_:x) : y ) = (0:x) : y
   step ( [_,[1,1],a] : (_:x) : y ) = (a+1:x) : y
   step ( (_:[2,i,j]:l) : (_:x) : y ) = (( l !! i ) : x) : y
   step ( (_:[3,f,vs,(g:gs)]:l) : (_:x) : y ) = (0:g:l) : (0:
   ...
   definition needs work, but point is it's a straightforward reified continuation interpreter
   prove that the transitive closure includes ( EVAL f x1 x2 x3 ... ) : C --> ( RET v ) : C iff f(x1,x2,x3,...) = v and v e. NN0
   use a single RecSea to build a general recursive function which searches for ( RET v ) in the closure of ( EVAL f x ), and returns it
   thus:
$)

eval-recursive $p |- ( x e. ( NN0 ^m ( 1 ... 2 ) ) |-> if ( ( x ` 1 ) e. dom RecArithGeneral , ( ( RecArithGeneral ` ( x ` 1 ) ) ` ( { 1 } X. { ( x ` 2 ) } ) ) , ( Undef ` NN0 ) ) ) e. RecArithGeneral $= ? $.

$( ---- DIOPHANTINE ---- $)
$( Define Diophantine sets and relations.  Prove composition laws and important cases like the exponential relation. $)

$( ---- MATIJASEVICH 1 ---- $)
$( Diophantine sets are semidecidable because polynomial functions are computable. $)

$( ---- MATIJASEVICH 2 ---- $)
$( Semidecidable sets are decidable by Turing machines, which can be expressed as vectorial and thus exponential satisfaction problems and are Diophantine. $)

$( ---- MATIJASEVICH 3 ---- $)
$( Diophantine <-> Semidecidable.  There exist non-decidable diophantine sets. $)
