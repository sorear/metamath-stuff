$[ set_clean.mm $]

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Stefan O'Rear
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Stuff copied from other mathboxen XXX - KEEP
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( the next two are needed at least until pellex is rewritten to use || $)

  $( ` A ` is divisible by ` B ` iff its negative is.  (Contributed by Jeff
     Madsen, 2-Sep-2009.) $)
  negmod0 $p |- ( ( A e. RR /\ B e. RR+ ) ->
                    ( ( A mod B ) = 0 <-> ( -u A mod B ) = 0 ) ) $=
    ( cr wcel crp wa cdiv co cz cneg cmo wceq znegcl cc rerpdivcl eleq1d adantl
    cc0 recn mod0 negneg 3syl syl5ib impbid2 wne adantr rpcn rpne0 divneg bitrd
    syl3anc wb renegcl sylan 3bitr4d ) ACDZBEDZFZABGHZIDZAJZBGHZIDZABKHRLVABKHR
    LZURUTUSJZIDZVCURUTVFUSMVFVEJZIDURUTVEMURVGUSIURUSCDUSNDVGUSLABOUSSUSUAUBPU
    CUDURVEVBIURANDZBNDZBRUEZVEVBLUPVHUQASUFUQVIUPBUGQUQVJUPBUHQABUIUKPUJABTUPV
    ACDUQVDVCULAUMVABTUNUO $.
    $( [2-Sep-2009] $)

  $( ` A ` is divisible by ` B ` iff its absolute value is.  (Contributed by
     Jeff Madsen, 2-Sep-2009.) $)
  absmod0 $p |- ( ( A e. RR /\ B e. RR+ ) ->
                    ( ( A mod B ) = 0 <-> ( ( abs ` A ) mod B ) = 0 ) ) $=
    ( cr wcel crp wa cabs cfv wceq cneg wo cmo co cc0 wb absor adantr wi eqeq1d
    oveq1 eqcoms a1i negmod0 bibi2d syl5ibrcom jaod mpd ) ACDZBEDZFZAGHZAIZUKAJ
    ZIZKZABLMZNIZUKBLMZNIZOZUHUOUIAPQUJULUTUNULUTRUJULUPURNUPURIAUKAUKBLTUASUBU
    JUTUNUQUMBLMZNIZOABUCUNUSVBUQUNURVANUKUMBLTSUDUEUFUG $.
    $( [2-Sep-2009] $)

$( JUSTIFICATION: used to prove ZZ-hood in modabsdifz by showing that the number differs at most in sign from an integer $)

  $( A real number is an integer iff its absolute value is an integer.
     (Contributed by Jeff Madsen, 2-Sep-2009.) $)
  absz $p |- ( A e. RR -> ( A e. ZZ <-> ( abs ` A ) e. ZZ ) ) $=
    ( cr wcel cz cabs cfv cn0 nn0abscl nn0z syl wceq cneg wo absor eleq1 biimpd
    wi a1i znegcl cc recn negneg eleq1d syl5ib syl9r jaod mpd impbid2 ) ABCZADC
    ZAEFZDCZUJUKGCULAHUKIJUIUKAKZUKALZKZMULUJQZANUIUMUPUOUMUPQUIUMULUJUKADOPRUO
    ULUNDCZUIUJUOULUQUKUNDOPUQUNLZDCUIUJUNSUIURADUIATCURAKAUAAUBJUCUDUEUFUGUH
    $.
    $( [2-Sep-2009] $)


$( JUSTIFICATION: split a set in two by definable predicate, easily show that the pieces "match up" with "no overlap" $)

  ${
    $d A x $.
    $( Law of excluded middle, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)
    rabxm $p |- A = ( { x e. A | ph } u. { x e. A | -. ph } ) $=
      ( wn wo crab cun wceq rabid2 cv wcel exmid a1i mprgbir unrab eqtr4i ) CAA
      DZEZBCFZABCFQBCFGCSHRBCRBCIRBJCKALMNAQBCOP $.
      $( [20-Jun-2011] $)

    $( Law of noncontradiction, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)
    rabnc $p |- ( { x e. A | ph } i^i { x e. A | -. ph } ) = (/) $=
      ( crab wn cin wa c0 inrab wceq rabeq0 cv wcel pm3.24 a1i mprgbir eqtri )
      ABCDAEZBCDFARGZBCDZHARBCITHJSEZBCSBCKUABLCMANOPQ $.
      $( [20-Jun-2011] $)
  $}

  ${
    $d A x y $.  $d B y $.
    dmmptss.1 $e |- F = ( x e. A |-> B ) $.
    $( The domain of a mapping is a subset of its base class.  (Contributed by
       Scott Fenton, 17-Jun-2013.) $)
    dmmptss $p |- dom F C_ A $=
      ( vy cdm cv wcel wceq wa copab cmpt df-mpt eqtri dmeqi dmopabss eqsstri )
      DGAHBIFHCJZKAFLZGBDTDABCMTEAFBCNOPSAFBQR $.
      $( [17-Jun-2013] $)
  $}


  $( Restricted specialization.  (Contributed by FL, 4-Jun-2012.) $)
  ra42e $p |- ( ( x e. A /\ y e. B /\ ph ) -> E. x e. A E. y e. B ph ) $=
    ( cv wcel w3a wrex wa wex simp1 ra4e 3adant1 19.8a syl2anc df-rex sylibr )
    BFDGZCFEGZAHZSACEIZJZBKZUBBDIUASUBUDSTALTAUBSACEMNUCBOPUBBDQR $.
    $( [4-Jun-2012] $)

  ${
    $d x y z $.
    $( Two ways to state the domain of an operation.  (Contributed by FL,
       24-Jan-2010.) $)
    twsvbdop $p |-
      { <. <. x , y >. , z >. | ( <. x , y >. e. ( A X. B ) /\ ph ) } =
        { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $=
      ( cv cop cxp wcel wa vex opelxp anbi1i oprabbii ) BGZCGZHEFIJZAKPEJQFJKZA
      KBCDRSAPQEFCLMNO $.
      $( [24-Jan-2010] $)
  $}

  ${
    $d A x $.  $d B x $.  $d X x $.
    $( The value of a union when the argument is in the first domain.
       (Contributed by Scott Fenton, 29-Jun-2013.) $)
    fvun1 $p |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. A ) ) ->
    ( ( F u. G ) ` X ) = ( F ` X ) ) $=
      ( vx wfn cin c0 wceq wcel wa w3a cun cfv wfun cdm fnfun fndm wn ineqan12d
      3ad2ant1 3ad2ant2 eqeq1d biimprd adantrd 3impia fvun syl21anc cv wi eleq1
      wral disj notbid rcla4cv sylbi imp adantl wb eleq2d adantr mtbird 3adant1
      ndmfv syl uneq2d un0 syl6eq eqtrd ) CAGZDBGZABHZIJZEAKZLZMZECDNOZECOZEDOZ
      NZVSVQCPZDPZCQZDQZHZIJZVRWAJVKVLWBVPACRUBVLVKWCVPBDRUCVKVLVPWGVKVLLZVNWGV
      OWHWGVNWHWFVMIVKVLWDAWEBACSBDSZUAUDUEUFUGECDUHUIVQWAVSINVSVQVTIVSVQEWEKZT
      ZVTIJVLVPWKVKVLVPLWJEBKZVPWLTZVLVNVOWMVNFUJZBKZTZFAUMVOWMUKFABUNWPWMFEAWN
      EJWOWLWNEBULUOUPUQURUSVLWJWLUTVPVLWEBEWIVAVBVCVDEDVEVFVGVSVHVIVJ $.
      $( [29-Jun-2013] $)
  $}

  $( The value of a union when the argument is in the second domain.
     (Contributed by Scott Fenton, 29-Jun-2013.) $)
  fvun2 $p |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. B ) ) ->
    ( ( F u. G ) ` X ) = ( G ` X ) ) $=
    ( wfn cin c0 wceq wcel w3a cun cfv uncom fveq1i incom eqeq1i anbi1i fvun1
    wa syl3an3b 3com12 syl5eq ) CAFZDBFZABGZHIZEBJZTZKECDLZMEDCLZMZEDMZEUJUKCDN
    OUEUDUIULUMIZUIUEUDBAGZHIZUHTUNUGUPUHUFUOHABPQRBADCESUAUBUC $.
    $( [29-Jun-2013] $)
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Miscellanea 1. Map utilities
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( rather old, potentially worth reproving $)
  ${
    constmap.1 $e |- A e. _V $.
    constmap.2 $e |- B e. _V $.
    constmap.3 $e |- C e. _V $.
    $( A constant (represented without dummy variables) is an element of a
       function set.

       _Note:  In the following development, we will be quite often quantifying
       over functions and points in N-dimensional space (which are equivalent
       to functions from an "index set").  Many of the following theorems exist
       to transfer standard facts about functions to elements of function
       sets._ $)
    constmap $p |- ( B e. C -> ( A X. { B } ) e. ( C ^m A ) ) $=
      ( wcel csn cmap co cxp wss snssi mapss syl wf fconst snex elmap mpbir a1i
      sseldd ) BCGZBHZAIJZCAIJZAUDKZUCUDCLUEUFLBCMUDCAFDNOUGUEGZUCUHAUDUGPABEQU
      DAUGBRDSTUAUB $.
      $( [30-Aug-2014] $)
  $}

  ${
    mapco2.1 $e |- B e. _V $.
    mapco2.2 $e |- C e. _V $.
    mapco2.3 $e |- E e. _V $.
    $( Post-composition (renaming indexes) of a mapping viewed as a point. $)
    mapco2 $p |- ( ( A e. ( B ^m C ) /\ D : E --> C ) -> ( A o. D ) e. ( B ^m E
        ) ) $=
      ( cmap co wcel wf wa ccom elmap biimpi fco sylan sylibr ) ABCIJKZECDLZMEB
      ADNZLZUBBEIJKTCBALZUAUCTUDBCAFGOPECBADQRBEUBFHOS $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d a b c d $.
    $( Eliminate antecedent for mapping theorems: domain can be taken to be a
       set. $)
    elmapex1 $p |- ( A e. ( B ^m C ) -> B e. _V ) $=
      ( va vb vd vc cmap co wcel c0 wceq wn cvv n0i cdm wrel cv wa wf cab cmpt2
      copab2 reldmoprab df-map df-mpt2 eqtri dmeqi releqi mpbir ovprc1 con1i
      syl ) ABCHIZJUNKLZMBNJZUNAOUPUOBCHHPZQDRZNJERZNJSFRUSURGRTGUAZLSZDEFUCZPZ
      QVADEFUDUQVCHVBHDENNUTUBVBDEGUEDEFNNUTUFUGUHUIUJUKULUM $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A c $.  $d B c $.  $d C c $.
    $( A mapping always has some domain, even if the notional domain is a
       proper class.  Uses ~ ovprc2 inessentially. $)
    elmapex2 $p |- ( A e. ( B ^m C ) -> E. c A e. ( B ^m c ) ) $=
      ( cvv wcel cmap co cv wex wi wceq oveq2 eleq2d cla4egv wn ovprc2 elmapex1
      mpcom syl6bi pm2.61i ) CEFZABCGHZFZABDIZGHZFZDJZKUGUDDCEUECLUFUCAUECBGMNO
      UBPZUDABBGHZFZUHUIUCUJABCGQNBEFUKUHABBRUGUKDBEUEBLUFUJAUEBBGMNOSTUA $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A c $.  $d B c $.  $d C c $.
    $( A mapping is always a function (even if C is a proper class) $)
    elmapfun $p |- ( A e. ( B ^m C ) -> Fun A ) $=
      ( vc cmap co wcel cv wex wfun elmapex2 wf cvv elmapex1 vex elmapg sylancl
      id wb syl mpbid ffun exlimiv ) ABCEFGABDHZEFGZDIAJZABCDKUEUFDUEUDBALZUFUE
      UEUGUERUEBMGUDMGUEUGSABUDNDOBUDAMMPQUAUDBAUBTUCT $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b c $.  $d B a b c $.  $d C a b c $.  $d D a b c $.  $d E a b c $.
    $( Renaming indexes in a tuple, with sethood as antecedents. $)
    mapco2g $p |- ( ( ( E e. _V /\ C e. _V ) /\ ( A e. ( B ^m C ) /\ D : E -->
        C ) ) -> ( A o. D ) e. ( B ^m E ) ) $=
      ( vb va vc cvv wcel wa cmap co wf cv wi wceq oveq2 eleq2d vex ccom anbi2d
      feq2 imbi12d feq3 anbi12d imbi1d elmapex1 oveq1 anbi1d mapco2 syl anabsi5
      vtoclg vtocl2g imp ) EIJCIJKABCLMZJZECDNZKZADUAZBELMZJZABFOZLMZJZGOZVDDNZ
      KZVABVGLMZJZPZVFEVDDNZKZVCPUTVCPGFECIIVGEQZVIVNVKVCVOVHVMVFVGEVDDUCUBVOVJ
      VBVAVGEBLRSUDVDCQZVNUTVCVPVFURVMUSVPVEUQAVDCBLRSVDCEDUEUFUGVFVHVKVFBIJVLA
      BVDUHAHOZVDLMZJZVHKZVAVQVGLMZJZPVLHBIVQBQZVTVIWBVKWCVSVFVHWCVRVEAVQBVDLUI
      SUJWCWAVJVAVQBVGLUISUDAVQVDDVGHTFTGTUKUNULUMUOUP $.
      $( [9-Oct-2014] $)
  $}

  $( A restricted mapping is a mapping. $)
  elmapssres $p |- ( ( A e. ( B ^m C ) /\ D C_ C /\ C e. _V ) -> ( A |` D ) e.
      ( B ^m D ) ) $=
    ( cmap co wcel wss cvv w3a cres wf simp1 wb elmapex1 3ad2ant1 simp3 syl2anc
    elmapg mpbid simp2 fssres ssexg 3adant1 mpbird ) ABCEFGZDCHZCIGZJZADKZBDEFG
    ZDBUJLZUICBALZUGULUIUFUMUFUGUHMUIBIGZUHUFUMNUFUGUNUHABCOPZUFUGUHQBCAIISRTUF
    UGUHUACBDAUBRUIUNDIGZUKULNUOUGUHUPUFDCIUCUDBDUJIISRUE $.
    $( [9-Oct-2014] $)

  $( A mapping is a function, forward direction only with superfluous
     antecedent removed. $)
  elmapi $p |- ( ( C e. _V /\ A e. ( B ^m C ) ) -> A : C --> B ) $=
    ( cvv wcel cmap co wa wf simpr elmapex1 adantl simpl elmapg syl2anc mpbid
    wb ) CDEZABCFGEZHZSCBAIZRSJTBDEZRSUAQSUBRABCKLRSMBCADDNOP $.
    $( [10-Oct-2014] $)

  ${
    $d N a b c x $.  $d A a b c x $.  $d B a b c x $.  $d C a b c x $.
    $d D a b c x $.  $d M a b c x $.
    mapfzcons.1 $e |- M = ( N + 1 ) $.
    $( Extending a one-based mapping by adding a tuple at the end results in
       another mapping. $)
    mapfzcons $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> (
        A u. { <. M , C >. } ) e. ( B ^m ( 1 ... M ) ) ) $=
      ( cn0 wcel c1 cfz co cmap caddc csn cun wf wceq cvv ovex cuz w3a c0 simp2
      cop cin wb elmapex1 3ad2ant2 elmapg sylancl mpbid wss wf1o f1osng sylancr
      simp3 f1of syl snssi 3ad2ant3 fss syl2anc fzp1disj 3ad2ant1 syl21anc cmin
      fun cz cfv 1z cc0 ax-1cn subidi fveq2i eqtr4i eleq2i biimpi fzsuc2 eqcomd
      nn0uz unidm a1i feq23d mpbird opeq1i sneqi uneq2i oveq2i eleq12i sylibr )
      EGHZABIEJKZLKHZCBHZUAZAEIMKZCUDZNZOZBIWPJKZLKZHZADCUDZNZOZBIDJKZLKZHWOXBW
      TBWSPZWOWLWPNZOZBBOZWSPZXHWOWLBAPZXIBWRPZWLXIUEUBQZXLWOWMXMWKWMWNUCWOBRHZ
      WLRHWMXMUFWMWKXPWNABWLUGUHZIEJSBWLARRUIUJUKWOXICNZWRPZXRBULZXNWOXIXRWRUMZ
      XSWOWPRHWNYAEIMSWKWMWNUPWPCRBUNUOXIXRWRUQURWNWKXTWMCBUSUTXIXRBWRVAVBWKWMX
      OWNIEGVCVDWLXIBBAWRVGVEWOXJXKWTBWSWOWTXJWOIVHHEIIVFKZTVIZHZWTXJQVJWKWMYDW
      NWKYDGYCEGVKTVIYCVTYBVKTIVLVMVNVOVPVQVDIEVRUOVSXKBQWOBWAWBWCUKWOXPWTRHXBX
      HUFXQIWPJSBWTWSRRUIUJWDXEWSXGXAXDWRAXCWQDWPCFWEWFWGXFWTBLDWPIJFWHWHWIWJ
      $.
      $( [10-Oct-2014] $)

    $( Recover prefix mapping from an extended mapping. $)
    mapfzcons1 $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> (
        ( A u. { <. M , C >. } ) |` ( 1 ... N ) ) = A ) $=
      ( cn0 wcel c1 cfz co csn cun cres c0 wceq cdm cin eqtri syl5eq w3a cop wf
      cmap resundir wfn cvv ovex elmapi mpan fnresdm 3syl 3ad2ant2 caddc dmsnop
      ffn dmres sneqi ineq2i fzp1disj 3ad2ant1 wrel relres reldm0 ax-mp uneq12d
      wb sylibr un0 syl6eq ) EGHZABIEJKZUDKHZCBHZUAZADCUBLZMVLNAVLNZVPVLNZMZAAV
      PVLUEVOVSAOMAVOVQAVROVMVKVQAPZVNVMVLBAUCZAVLUFVTVLUGHVMWAIEJUHABVLUIUJVLB
      AUPVLAUKULUMVOVRQZOPZVROPZVOWBVLEIUNKZLZRZOWBVLVPQZRWGVPVLUQWHWFVLWHDLWFD
      CUODWEFURSUSSVKVMWGOPVNIEGUTVATVRVBWDWCVGVPVLVCVRVDVEVHVFAVIVJT $.
      $( [10-Oct-2014] $)

    $( A nonempty mapping has a prefix. $)
    mapfzcons1cl $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... M ) ) ) -> ( A |` (
        1 ... N ) ) e. ( B ^m ( 1 ... N ) ) ) $=
      ( cn0 wcel c1 cfz co cmap wa wss cres simpr caddc fzssp1 oveq2i syl6sseqr
      cvv adantr ovex a1i elmapssres syl3anc ) DFGZABHCIJZKJGZLZUHHDIJZUGMZUGTG
      ZAUJNBUJKJGUFUHOUFUKUHUFUJHDHPJZIJUGHDFQCUMHIERSUAULUIHCIUBUCABUGUJUDUE
      $.
      $( [10-Oct-2014] $)

    $( Recover added element from an extended mapping. $)
    mapfzcons2 $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> (
        ( A u. { <. M , C >. } ) ` M ) = C ) $=
      ( cn0 wcel c1 cfz co csn cfv wfn cin c0 wceq cvv ovex caddc w3a wf elmapi
      cmap cop cun mpan ffn syl 3ad2ant2 eqeltri fnsn a1i sneqi ineq2i fzp1disj
      syl5eq 3ad2ant1 snid fvun2 syl112anc simp3 fvsng sylancr eqtrd ) EGHZABIE
      JKZUDKHZCBHZUAZDADCUELZUFMZDVKMZCVJAVGNZVKDLZNZVGVOOZPQZDVOHZVLVMQVHVFVNV
      IVHVGBAUBZVNVGRHVHVTIEJSABVGUCUGVGBAUHUIUJVPVJDCDEITKZRFEITSUKZULUMVFVHVR
      VIVFVQVGWALZOPVOWCVGDWAFUNUOIEGUPUQURVSVJDWBUSUMVGVOAVKDUTVAVJDRHVIVMCQWB
      VFVHVIVBDCRBVCVDVE $.
      $( [10-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Miscellanea for polynomials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x a b $.  $d V a b $.  $d B a b $.  $d C a b $.  $d R a b x $.
    $( Value of a pointwise operation on two functions defined using maps-to
       notation. $)
    ofmpteq $p |- ( ( A e. V /\ ( x e. A |-> B ) Fn A /\ ( x e. A |-> C ) Fn A
        ) ->
        ( ( x e. A |-> B ) oF R ( x e. A |-> C ) ) = ( x e. A |-> ( B R C ) ) )
        $=
      ( va vb wcel cmpt wfn co cv csb cvv wral eqid mptfng ax-17 cbvmpt w3a cof
      simp1 simpr simpl2 sylibr vex ax17el hbcsb1 hbel weq csbeq1a eleq1d rcla4
      wa sylc simpl3 wceq a1i offval2 hbov oveq12d syl6eqr ) BFIZABCJZBKZABDJZB
      KZUAZVEVGEUBLGBAGMZCNZAVJDNZELZJABCDELZJVIGBVKVLEVEVGFOOVDVFVHUCVIVJBIZUO
      ZVOCOIZABPZVKOIZVIVOUDZVPVFVRVDVFVHVOUEABCVEVEQRUFVQVSAVJBAHHVKOAHVJCGUGZ
      HGAUHZUIZHMZOIASZUJAGUKZCVKOAVJCULZUMUNUPVPVODOIZABPZVLOIZVTVPVHWIVDVFVHV
      OUQABDVGVGQRUFWHWJAVJBAHHVLOAHVJDWAWBUIZWEUJWFDVLOAVJDULZUMUNUPVEGBVKJURV
      IAGHBCVKWDCIGSWCWGTUSVGGBVLJURVIAGHBDVLWDDIGSWKWLTUSUTAGHBVNVMWDVNIGSAHVK
      VLEWCWDEIASWKVAWFCVKDVLEWGWLVBTVC $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d A t $.  $d C t $.
    $( Interpret range of a maps-to notation as a constraint on the
       definition. $)
    mptfcl $p |- ( ( t e. A |-> B ) : A --> C -> ( t e. A -> B e. C ) ) $=
      ( cmpt wf wcel wral cv wi eqid fmpt ra4 sylbir ) BDABCEZFCDGZABHAIBGPJABD
      COOKLPABMN $.
      $( [10-Oct-2014] $)
  $}


  ${
    $d F a b c $.  $d A a b c $.  $d G a b c $.  $d V a b c $.  $d X a b c $.
    $d R a b c $.

    $( Function value of a pointwise composition. $)
    fnfvof $p |- ( ( ( F Fn A /\ G Fn A ) /\ ( A e. V /\ X e. A ) ) ->
        ( ( F oF R G ) ` X ) = ( ( F ` X ) R ( G ` X ) ) ) $=
      ( vc va vb wfn wa wcel co cfv cdm cin cv cmpt cvv wceq cof fnex ad2ant2lr
      ad2ant2r fndm ineqan12d adantr inidm syl6eq simprl mptexg syl dmeq ineq1d
      eqeltrd fveq1 oveq1d mpteq12dv ineq2d oveq2d df-of ovmpt2g syl3anc fveq1d
      simprr eleqtrrd fveq2 oveq12d eqid ovex fvmpt eqtrd ) CAJZDAJZKZAELZFALZK
      ZKZFCDBUAZMZNFGCOZDOZPZGQZCNZWEDNZBMZRZNZFCNZFDNZBMZVSFWAWIVSCSLZDSLZWISL
      ZWAWITVMVPWNVNVQAECUBUDVNVPWOVMVQAEDUBUCVSWDELWPVSWDAEVSWDAAPZAVOWDWQTVRV
      MVNWBAWCAACUEADUEUFUGAUHUIZVOVPVQUJUOGWDWHEUKULHICDSSGHQZOZIQZOZPZWEWSNZW
      EXANZBMZRWIVTGWBXBPZWFXEBMZRSWSCTZGXCXFXGXHXIWTWBXBWSCUMUNXIXDWFXEBWEWSCU
      PUQURXADTZGXGXHWDWHXJXBWCWBXADUMUSXJXEWGWFBWEXADUPUTURGBHIVAVBVCVDVSFWDLW
      JWMTVSFAWDVOVPVQVEWRVFGFWHWMWDWIWEFTWFWKWGWLBWEFCVGWEFDVGVHWIVIWKWLBVJVKU
      LVL $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d B x $.  $d A x $.  $d C x $.
    $( Express composition of two functions as a maps-to applying both in
       sequence. $)
    fcompt $p |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |->
        ( A ` ( B ` x ) ) ) ) $=
      ( wf wa ccom cv cfv cmpt wfn wceq crn wss ffn adantr adantl frn fnco wfun
      syl3anc dffn5v sylib ffun wcel fvco2 3expa mpteq2dva syl2anc eqtrd ) EFBG
      ZDECGZHZBCIZADAJZUPKZLZADUQCKBKZLZUOUPDMZUPUSNUOBEMZCDMZCOEPZVBUMVCUNEFBQ
      RUNVDUMDECQSZUNVEUMDECTSEDBCUAUCADUPUDUEUOBUBZVDUSVANUMVGUNEFBUFRVFVGVDHA
      DURUTVGVDUQDUGURUTNDUQBCUHUIUJUKUL $.
      $( [5-Oct-2014] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Multivariate polynomials over the integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c mzPolyCld $.
  $c mzPoly $.
  $( Extend class notation to include pre-polynomial rings. $)
  cmzpcl $a class mzPolyCld $.
  $( Extend class notation to include polynomial rings. $)
  cmzp $a class mzPoly $.

  ${
    $d v p f g $.  $d v p i $.  $d v p j x $.

    $( Define the polynomially closed function rings over an arbitrary index
       set ` v ` .  The set ` ( mzPolyCld `` v ) ` contains all sets of
       functions from ` ( ZZ ^m v ) ` to ` ZZ ` which include all constants and
       projections and are closed under addition and multiplication.  This is a
       "temporary" set used to define the polynomial function ring itself
       ` ( mzPoly `` v ) ` ; see ~ df-mzp . $)
    df-mzpcl $a |- mzPolyCld = ( v e. _V |-> { p | ( p C_ ( ZZ ^m ( ZZ ^m v ) )
        /\
        ( ( A. i e. ZZ ( ( ZZ ^m v ) X. { i } ) e. p
           /\ A. j e. v ( x e. ( ZZ ^m v ) |-> ( x ` j ) ) e. p )
        /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) )
        } ) $.

    $( Polynomials over ` ZZ ` with an arbitrary index set, that is, the
       smallest ring of functions containing all constant functions and all
       projections.  This is almost the most general reasonable definition; to
       reach full generality, we would need to be able to replace ZZ with an
       arbitrary (semi-)ring (and a coordinate subring), but rings have not
       been defined yet. $)
    df-mzp $a |- mzPoly = ( v e. _V |-> |^| ( mzPolyCld ` v ) ) $.
  $}

  ${
    $d V v p f g $.  $d V v p i $.  $d V v p j x $.
    $( Substitution lemma for ` mzPolyCld ` . $)
    mzpclval $p |- ( V e. _V -> ( mzPolyCld ` V ) = { p | ( p C_ ( ZZ ^m ( ZZ
        ^m V ) ) /\
        ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. p
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. p )
        /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) )
        } ) $=
      ( vv cv cz cmap co wss cxp wcel wral cmpt wa cvv wceq csn cfv cmul cmzpcl
      caddc cof cab oveq2 oveq2d sseq2d xpeq1d eleq1d ralbidv mpteq1 raleqbi1dv
      syl anbi12d anbi1d abbidv df-mzpcl ovex abssexg ax-mp fvmpt ) HFGIZJJHIZK
      LZKLZMZVGDIUAZNZVEOZDJPZAVGEIAIUBZQZVEOZEVFPZRZBIZCIZUEUFLVEOVSVTUCUFLVEO
      RCVEPBVEPZRZRZGUGVEJJFKLZKLZMZWDVJNZVEOZDJPZAWDVNQZVEOZEFPZRZWARZRZGUGZSU
      DVFFTZWCWOGWQVIWFWBWNWQVHWEVEWQVGWDJKVFFJKUHZUIUJWQVRWMWAWQVMWIVQWLWQVLWH
      DJWQVKWGVEWQVGWDVJWRUKULUMVPWKEVFFWQVOWJVEWQVGWDTVOWJTWRAVGWDVNUNUPULUOUQ
      URUQUSAHBCDEGUTWESOWPSOJWDKVAWNGWESVBVCVD $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d V v p f g $.  $d V v p i $.  $d V v p j x $.  $d P v p f g $.
    $d P v p i $.  $d P v p j x $.
    $( Double substitution lemma for ` mzPolyCld ` . $)
    elmzpcl $p |- ( ( V e. _V /\ P e. _V ) -> ( P e. ( mzPolyCld ` V ) <-> ( P
        C_ ( ZZ ^m ( ZZ ^m V ) ) /\
        ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. P
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. P )
        /\ A. f e. P A. g e. P ( ( f oF + g ) e. P /\ ( f oF x. g ) e. P ) ) )
        ) ) $=
      ( vp cvv wcel cfv cv cz cmap co wral wa wb eleq2 anbi12d wss csn cxp cmpt
      cmzpcl caddc cof cmul mzpclval eleq2d wceq sseq1 ralbidv raleqbi1dv elabg
      cab bitr syl2an ) GIJZBGUEKZJZBHLZMMGNOZNOZUAZVCELUBUCZVBJZEMPZAVCFLALKUD
      ZVBJZFGPZQZCLZDLZUFUGOZVBJZVMVNUHUGOZVBJZQZDVBPZCVBPZQZQZHUPZJZRWEBVDUAZV
      FBJZEMPZVIBJZFGPZQZVOBJZVQBJZQZDBPZCBPZQZQZRVAWRRBIJUSUTWDBACDEFGHUIUJWCW
      RHBIVBBUKZVEWFWBWQVBBVDULWSVLWKWAWPWSVHWHVKWJWSVGWGEMVBBVFSUMWSVJWIFGVBBV
      ISUMTVTWOCVBBVSWNDVBBWSVPWLVRWMVBBVOSVBBVQSTUNUNTTUOVAWEWRUQUR $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d V v p f g a b $.  $d P v p f g a b $.  $d F v p f g a b $.
    $d G v p f g a b $.
    $( The set of all functions with the signature of a polynomial is a
       polynomially closed set.  This is a lemma to show that the intersection
       in ~ df-mzp is well defined. $)
    mzpclall $p |- ( V e. _V -> ( ZZ ^m ( ZZ ^m V ) ) e. ( mzPolyCld ` V ) ) $=
      ( vv vf vg va vb cz cv cmap co cmzpcl cfv wcel cvv wral wa caddc wf elmap
      zex wceq oveq2 fveq2 eleq12d wss csn cxp cmpt cof cmul ssid ovex constmap
      oveq2d vex rgen wel ffvelrn sylanb ancoms eqid fmptd sylibr pm3.2i zaddcl
      adantl simpl simpr a1i inidm off zmulcl anbi12i 3imtr4i rgen2a wb elmzpcl
      jca mp2an mpbir vtoclg ) GGBHZIJZIJZWBKLZMZGGAIJZIJZAKLZMBANWBAUAZWDWHWEW
      IWJWCWGGIWBAGIUBUNWBAKUCUDWFWDWDUEZWCCHZUFUGWDMZCGOZDWCWLDHZLZUHZWDMZCWBO
      ZPZWLWOQUIJZWDMZWLWOUJUIJZWDMZPZDWDOCWDOZPZPZWKXGWDUKWTXFWNWSWMCGWCWLGGWB
      IULZCUOTUMUPWRCWBCBUQZWCGWQRWRXJDWCWPGWQWOWCMZXJWPGMZXKWBGWORXJXLGWBWOTBU
      OZSWBGWLWOURUSUTWQVAVBGWCWQTXISVCUPVDXECDWDWCGWLRZWCGWORZPZWCGXARZWCGXCRZ
      PWLWDMZWOWDMZPXEXPXQXRXPEFWCWCWCQGGGWLWONNEHZGMFHZGMPZYAYBQJGMXPYAYBVEVFX
      NXOVGZXNXOVHZWCNMXPXIVIZYFWCVJZVKXPEFWCWCWCUJGGGWLWONNYCYAYBUJJGMXPYAYBVL
      VFYDYEYFYFYGVKVRXSXNXTXOGWCWLTXISGWCWOTXISVMXBXQXDXRGWCXATXISGWCXCTXISVMV
      NVOVDVDWBNMWDNMWFXHVPXMGWCIULDWDCDCCWBVQVSVTWA $.
      $( [4-Oct-2014] $)

    $( Corrolary of ~ mzpclall :  Polynomially closed function sets are not
       empty. $)
    mzpcln0 $p |- ( V e. _V -> ( mzPolyCld ` V ) =/= (/) ) $=
      ( cvv wcel cz cmap co cmzpcl cfv c0 wne mzpclall ne0i syl ) ABCDDAEFEFZAG
      HZCOIJAKONLM $.
      $( [4-Oct-2014] $)

    $( Defining property 1 of a polynomially closed function set ` P ` : it
       contains all constant functions. $)
    mzpcl1 $p |- ( ( V e. _V /\ P e. ( mzPolyCld ` V ) /\ F e. ZZ ) -> ( ( ZZ
        ^m V ) X. { F } ) e. P ) $=
      ( vf vg cvv wcel cmzpcl cfv cz w3a cmap co cv csn cxp wral wa cof syl2anc
      simp3 wss cmpt caddc cmul simp2 simp1 elex 3ad2ant2 elmzpcl mpbid simprll
      wb syl wceq sneq xpeq2d eleq1d rcla4va ) CFGZACHIZGZBJGZKZVCJCLMZDNZOZPZA
      GZDJQZVEBOZPZAGZUTVBVCUAVDAJVELMUBZVJEVEVFENZIUCAGDCQZRVFVOUDSMAGVFVOUESM
      AGREAQDAQZRRZVJVDVBVRUTVBVCUFVDUTAFGZVBVRUMUTVBVCUGVBUTVSVCAVAUHUIEADEDDC
      UJTUKVNVJVPVQULUNVIVMDBJVFBUOZVHVLAVTVGVKVEVFBUPUQURUST $.
      $( [4-Oct-2014] $)

    $( Defining property 2 of a polynomially closed function set ` P ` : it
       contains all projections. $)
    mzpcl2 $p |- ( ( V e. _V /\ P e. ( mzPolyCld ` V ) /\ F e. V ) -> ( g e. (
        ZZ ^m V ) |-> ( g ` F ) ) e. P ) $=
      ( vf cvv wcel cmzpcl cfv w3a cz cmap co cv cmpt wral wa cof syl2anc wceq
      simp3 wss csn cxp caddc cmul simp2 wb simp1 elex 3ad2ant2 elmzpcl simprlr
      mpbid syl fveq2 adantr mpteq2dva eleq1d rcla4va ) DFGZADHIZGZCDGZJZVDBKDL
      MZENZBNZIZOZAGZEDPZBVFCVHIZOZAGZVAVCVDUAVEAKVFLMUBZVFVGUCUDAGEKPZVLQVGVHU
      ERMAGVGVHUFRMAGQBAPEAPZQQZVLVEVCVSVAVCVDUGVEVAAFGZVCVSUHVAVCVDUIVCVAVTVDA
      VBUJUKBAEBEEDULSUNVPVQVLVRUMUOVKVOECDVGCTZVJVNAWABVFVIVMWAVIVMTVHVFGVGCVH
      UPUQURUSUTS $.
      $( [4-Oct-2014] $)

    $( Defining properties 2 of a polynomially closed function set ` P ` : it
       is closed under pointwise addition and multiplication. $)
    mzpcl34 $p |- ( ( V e. _V /\ P e. ( mzPolyCld ` V ) /\ ( F e. P /\ G e. P )
        ) -> ( ( F oF + G ) e. P /\ ( F oF x. G ) e. P ) ) $=
      ( vf vg cvv wcel cfv wa cv cof co wral cz cmap syl2anc wceq oveq1 eleq1d
      cmzpcl w3a caddc cmul simp3 wss csn cxp cmpt simp2 wb simp1 elex 3ad2ant2
      elmzpcl mpbid simprr syl anbi12d oveq2 rcla42va ) DGHZADUAIZHZBAHCAHJZUBZ
      VEEKZFKZUCLZMZAHZVGVHUDLZMZAHZJZFANEANZBCVIMZAHZBCVLMZAHZJZVBVDVEUEVFAOOD
      PMZPMUFZWBVGUGUHAHEONFWBVGVHIUIAHEDNJZVPJJZVPVFVDWEVBVDVEUJVFVBAGHZVDWEUK
      VBVDVEULVDVBWFVEAVCUMUNFAEFEEDUOQUPWCWDVPUQURVOWABVHVIMZAHZBVHVLMZAHZJEFB
      CAAVGBRZVKWHVNWJWKVJWGAVGBVHVISTWKVMWIAVGBVHVLSTUSVHCRZWHVRWJVTWLWGVQAVHC
      BVIUTTWLWIVSAVHCBVLUTTUSVAQ $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d V v p f g a b $.
    $( Value of the ` mzPoly ` function. $)
    mzpval $p |- ( V e. _V -> ( mzPoly ` V ) = |^| ( mzPolyCld ` V ) ) $=
      ( vv cvv wcel cmzpcl cfv cint cmzp wceq c0 wne mzpcln0 intex sylib inteqd
      cv fveq2 df-mzp fvmptg mpdan ) ACDZAEFZGZCDZAHFUCIUAUBJKUDALUBMNBABPZEFZG
      UCCCHUEAIUFUBUEAEQOBRST $.
      $( [4-Oct-2014] $)

    $( ` mzPoly ` is defined for all index sets which are sets.  This is used
       with ~ elfvdm to eliminate sethood antecedents. $)
    dmmzp $p |- dom mzPoly = _V $=
      ( vv cmzp cdm cvv cv cmzpcl cfv cint cmpt df-mzp dmeqi wcel dmmptg c0 wne
      wceq mzpcln0 intex sylib mprg eqtri ) BCADAEZFGZHZIZCZDBUEAJKUDDLZUFDPADA
      DUDDMUBDLUCNOUGUBQUCRSTUA $.
      $( [4-Oct-2014] $)

    $( Polynomial closedness is a universal first-order property and passes to
       intersections.  This is where the closure properties of the polynomial
       ring itself are proved. $)
    mzpincl $p |- ( V e. _V -> ( mzPoly ` V ) e. ( mzPolyCld ` V ) ) $=
      ( vf vg va cvv wcel cfv cz cmap co cv wral wa cof simpll simplr ralrimiva
      simpr ovex elint2 cmzp cmzpcl cint mzpval wss csn cxp cmpt caddc mzpclall
      cmul intss1 syl mzpcl1 syl3anc snex xpex sylibr mzpcl2 jca mzpcl34 3expia
      mptex wel ralimdva r19.26 3imtr3g vex anbi12i 3imtr4g ralrimivv jca32 wne
      wb c0 mzpcln0 intex sylib elmzpcl mpdan mpbird eqeltrd ) AEFZAUAGAUBGZUCZ
      WDAUDWCWEWDFZWEHHAIJZIJZUEZWGBKZUFZUGZWEFZBHLZCWGWJCKZGZUHZWEFZBALZMZWJWO
      UINZJZWEFZWJWOUKNZJZWEFZMZCWELBWELZMMZWCWIWTXHWCWHWDFWIAUJWHWDULUMWCWNWSW
      CWMBHWCWJHFZMZWLDKZFZDWDLWMXKXMDWDXKXLWDFZMWCXNXJXMWCXJXNOXKXNRWCXJXNPXLW
      JAUNUOQDWLWDWGWKHAISZWJUPUQTURQWCWRBAWCWJAFZMZWQXLFZDWDLWRXQXRDWDXQXNMWCX
      NXPXRWCXPXNOXQXNRWCXPXNPXLCWJAUSUOQDWQWDCWGWPXOVCTURQUTWCXGBCWEWEWCBDVDZD
      WDLZCDVDZDWDLZMZXBXLFZDWDLZXEXLFZDWDLZMZWJWEFZWOWEFZMXGWCXSYAMZDWDLYDYFMZ
      DWDLYCYHWCYKYLDWDWCXNYKYLXLWJWOAVAVBVEXSYADWDVFYDYFDWDVFVGYIXTYJYBDWJWDBV
      HTDWOWDCVHTVIXCYEXFYGDXBWDWJWOXASTDXEWDWJWOXDSTVIVJVKVLWCWEEFZWFXIVNWCWDV
      OVMYMAVPWDVQVRCWEBCBBAVSVTWAWB $.
      $( [4-Oct-2014] $)
  $}

  $( Constant functions are polynomial.  See also ~ mzpconstmpt . $)
  mzpconst $p |- ( ( V e. _V /\ C e. ZZ ) -> ( ( ZZ ^m V ) X. { C } ) e. (
      mzPoly ` V ) ) $=
    ( cvv wcel cz wa cmzp cfv cmzpcl cmap co csn cxp simpl mzpincl adantr simpr
    mzpcl1 syl3anc ) BCDZAEDZFTBGHZBIHDZUAEBJKALMUBDTUANTUCUABOPTUAQUBABRS $.
    $( [4-Oct-2014] $)

  $( A polynomial function is a function from the coordinate space to the
     integers. $)
  mzpf $p |- ( F e. ( mzPoly ` V ) -> F : ( ZZ ^m V ) --> ZZ ) $=
    ( cmzp cfv wcel cz cmap co wf cvv wss cdm elfvdm dmmzp syl6eleq cmzpcl cint
    mzpval mzpclall syl intss1 eqsstrd sselda anidms zex ovex elmap sylib ) ABC
    DZEZAFFBGHZGHZEZUKFAIUJUMUJUIULAUJBJEZUIULKUJBCLJABCMNOUNUIBPDZQZULBRUNULUO
    EUPULKBSULUOUATUBTUCUDFUKAUEFBGUFUGUH $.
    $( [5-Oct-2014] $)

  ${
    $d X g $.  $d V g $.
    $( A projection function is polynomial. $)
    mzpproj $p |- ( ( V e. _V /\ X e. V ) -> ( g e. ( ZZ ^m V ) |-> ( g ` X ) )
        e. ( mzPoly ` V ) ) $=
      ( cvv wcel wa cmzp cfv cmzpcl cz cmap co cmpt simpl mzpincl adantr mzpcl2
      cv simpr syl3anc ) BDEZCBEZFUABGHZBIHEZUBAJBKLCARHMUCEUAUBNUAUDUBBOPUAUBS
      UCACBQT $.
      $( [4-Oct-2014] $)
  $}

  $( The pointwise sum of two polynomial functions is a polynomial function.
     See also ~ mzpaddmpt . $)
  mzpadd $p |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) -> ( A oF + B )
      e. ( mzPoly ` V ) ) $=
    ( cmzp cfv wcel wa caddc cof co cvv cmzpcl cdm elfvdm dmmzp syl6eleq adantr
    cmul mzpincl syl id mzpcl34 syl3anc simpld ) ACDEZFZBUEFZGZABHIJUEFZABRIJUE
    FZUHCKFZUECLEFZUHUIUJGUFUKUGUFCDMKACDNOPQZUHUKULUMCSTUHUAUEABCUBUCUD $.
    $( [4-Oct-2014] $)

  $( The pointwise product of two polynomial functions is a polynomial
     function.  See also ~ mzpmulmpt . $)
  mzpmul $p |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) -> ( A oF x. B
      ) e. ( mzPoly ` V ) ) $=
    ( cmzp cfv wcel wa caddc cof co cvv cmzpcl cdm elfvdm dmmzp syl6eleq adantr
    cmul mzpincl syl id mzpcl34 syl3anc simprd ) ACDEZFZBUEFZGZABHIJUEFZABRIJUE
    FZUHCKFZUECLEFZUHUIUJGUFUKUGUFCDMKACDNOPQZUHUKULUMCSTUHUAUEABCUBUCUD $.
    $( [4-Oct-2014] $)

  ${
    $d V x a b $.  $d C x $.  $d D x a b $.  $d A a b $.

    $( A constant function expressed in maps-to notation is polynomial.  This
       theorem and the several that follow ( ~ mzpaddmpt , ~ mzpmulmpt ,
       ~ mzpnegmpt , ~ mzpsubmpt , ~ mzpexpmpt ) can be used to build proofs
       that functions which are "manifestly polynomial", in the sense of being
       a maps-to containing constants, projections, and simple arithmetic
       operations, are actually polynomial functions.  There is no mzpprojmpt
       because ~ mzpproj is already expressed using maps-to notation. $)
    mzpconstmpt $p |- ( ( V e. _V /\ C e. ZZ ) -> ( x e. ( ZZ ^m V ) |-> C ) e.
        ( mzPoly ` V ) ) $=
      ( cvv wcel cz wa cmap cmpt csn cxp cmzp cfv fconstmpt mzpconst syl5eqelr
      co ) CDEBFEGAFCHQZBIRBJKCLMARBNBCOP $.
      $( [5-Oct-2014] $)

    $( Sum of polynomial functions is polynomial.  Maps-to version of
       ~ mzpadd . $)
    mzpaddmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e.
        ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A + B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel wa caddc cof wfn wf mzpf ffn syl cvv wceq
      ovex ofmpteq mp3an1 syl2an mzpadd eqeltrrd ) AEDFGZBHZDIJZKZAUHCHZUJKZLUI
      ULMNGZAUHBCMGHZUJUKUIUHOZULUHOZUNUOUAZUMUKUHEUIPUPUIDQUHEUIRSUMUHEULPUQUL
      DQUHEULRSUHTKUPUQUREDFUBAUHBCMTUCUDUEUIULDUFUG $.
      $( [5-Oct-2014] $)

    $( Product of polynomial functions is polynomial.  Maps-to version of
       ~ mzpmulmpt . $)
    mzpmulmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e.
        ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A x. B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel wa cmul cof wfn wf mzpf ffn syl cvv wceq
      ovex ofmpteq mp3an1 syl2an mzpmul eqeltrrd ) AEDFGZBHZDIJZKZAUHCHZUJKZLUI
      ULMNGZAUHBCMGHZUJUKUIUHOZULUHOZUNUOUAZUMUKUHEUIPUPUIDQUHEUIRSUMUHEULPUQUL
      DQUHEULRSUHTKUPUQUREDFUBAUHBCMTUCUDUEUIULDUFUG $.
      $( [5-Oct-2014] $)

    ${
      $d B a $.
      $( The difference of two polynomial functions is polynomial. $)
      mzpsubmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x
          e. ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
          ( x e. ( ZZ ^m V ) |-> ( A - B ) ) e. ( mzPoly ` V ) ) $=
        ( va cz co cmpt cmzp wcel wa c1 cneg caddc hbmpt1 cv hbel cc wceq zsscn
        cmap cfv cmin cmul ax-17 hban wf mzpf ad2antlr simpr mptfcl sylc sseldi
        mulm1 syl oveq2d ad2antrr negsub syl2anc eqtr2d mpteq2da cvv cdm elfvdm
        dmmzp syl6eleq nn0negzi mzpconstmpt sylancl mzpmulmpt mpancom mzpaddmpt
        1nn0 sylan2 eqeltrd ) AFDUAGZBHZDIUBZJZAVPCHZVRJZKZAVPBCUCGZHAVPBLMZCUD
        GZNGZHZVRWBAVPWCWFVSWAAAEEVQVRAEVPBOEPVRJAUEZQAEEVTVRAEVPCOWHQUFWBAPVPJ
        ZKZWFBCMZNGZWCWJWEWKBNWJCRJZWEWKSWJFRCTWJVPFVTUGZWICFJWAWNVSWIVTDUHUIWB
        WIUJZAVPCFUKULUMZCUNUOUPWJBRJWMWLWCSWJFRBTWJVPFVQUGZWIBFJVSWQWAWIVQDUHU
        QWOAVPBFUKULUMWPBCURUSUTVAWAVSAVPWEHVRJZWGVRJAVPWDHVRJZWAWRWADVBJWDFJWS
        WADIVCVBVTDIVDVEVFLVMVGAWDDVHVIAWDCDVJVKABWEDVLVNVO $.
        $( [10-Oct-2014] $)
    $}

    $( Negation of a polynomial function. $)
    mzpnegmpt $p |- ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) -> ( x e. (
        ZZ ^m V ) |-> -u A ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel cneg cc0 cmin df-neg mpteq2i elfvdm dmmzp
      cvv cdm syl6eleq 0z mzpconstmpt sylancl id1 mzpsubmpt syl2anc syl5eqel )
      ADCEFZBGZCHIZJZAUHBKZGAUHLBMFZGZUJAUHULUMBNOUKAUHLGUJJZUKUNUJJUKCRJLDJUOU
      KCHSRUICHPQTUAALCUBUCUKUDALBCUEUFUG $.
      $( [11-Oct-2014] $)

    $( Raise a polynomial function to a (fixed) exponent. $)
    mzpexpmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ D e.
        NN0 ) ->
        ( x e. ( ZZ ^m V ) |-> ( A ^ D ) ) e. ( mzPoly ` V ) ) $=
      ( va vb wcel cz co cmpt cexp wi wceq oveq2 adantr mpteq2dva eleq1d imbi2d
      c1 cc cn0 cmap cmzp cfv cv cc0 caddc weq wral wss mzpf zsscn sylancl eqid
      wf fss fmpt sylibr hbra1 wa ra4 imp exp0 syl mpteq2da cvv elfvdm syl6eleq
      cdm dmmzp 1z mzpconstmpt eqeltrd cmul 3ad2ant2 simp1 ax-17 adantlr simplr
      w3a hban expp1 syl2anc simp3 simp2 mzpmulmpt 3exp a2d nn0ind impcom ) CUA
      GAHDUBIZBJZDUCUDZGZAWKBCKIZJZWMGZWNAWKBEUEZKIZJZWMGZLWNAWKBUFKIZJZWMGZLWN
      AWKBFUEZKIZJZWMGZLWNAWKBXESUGIZKIZJZWMGZLWNWQLEFCWRUFMZXAXDWNXMWTXCWMXMAW
      KWSXBXMWSXBMAUEWKGZWRUFBKNOPQREFUHZXAXHWNXOWTXGWMXOAWKWSXFXOWSXFMXNWRXEBK
      NOPQRWRXIMZXAXLWNXPWTXKWMXPAWKWSXJXPWSXJMXNWRXIBKNOPQRWRCMZXAWQWNXQWTWPWM
      XQAWKWSWOXQWSWOMXNWRCBKNOPQRWNXCAWKSJZWMWNBTGZAWKUIZXCXRMWNWKTWLUOZXTWNWK
      HWLUOHTUJYAWLDUKULWKHTWLUPUMAWKTBWLWLUNUQURZXTAWKXBSXSAWKUSZXTXNUTXSXBSMX
      TXNXSXSAWKVAVBZBVCVDVEVDWNDVFGSHGXRWMGWNDUCVIVFWLDUCVGVJVHVKASDVLUMVMXEUA
      GZWNXHXLYEWNXHXLYEWNXHVTZXKAWKXFBVNIZJZWMYFXTYEXKYHMWNYEXTXHYBVOYEWNXHVPX
      TYEUTZAWKXJYGXTYEAYCYEAVQWAYIXNUTXSYEXJYGMXTXNXSYEYDVRXTYEXNVSBXEWBWCVEWC
      YFXHWNYHWMGYEWNXHWDYEWNXHWEAXFBDWFWCVMWGWHWIWJ $.
      $( [5-Oct-2014] $)

  $}

  ${
    $d ph x f g $.  $d ps f g $.  $d ch x $.  $d th x $.  $d ta x $.
    $d et x $.  $d ze x $.  $d si x $.  $d rh x $.  $d V x f g a b $.
    $d A x $.
    mzpindd.co $e |- ( ( ph /\ f e. ZZ ) -> ch ) $.
    mzpindd.pr $e |- ( ( ph /\ f e. V ) -> th ) $.
    mzpindd.ad $e |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ
        ^m V ) --> ZZ /\ et ) ) -> ze ) $.
    mzpindd.mu $e |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ
        ^m V ) --> ZZ /\ et ) ) -> si ) $.
    mzpindd.1 $e |- ( x = ( ( ZZ ^m V ) X. { f } ) -> ( ps <-> ch ) ) $.
    mzpindd.2 $e |- ( x = ( g e. ( ZZ ^m V ) |-> ( g ` f ) ) -> ( ps <-> th ) )
        $.
    mzpindd.3 $e |- ( x = f -> ( ps <-> ta ) ) $.
    mzpindd.4 $e |- ( x = g -> ( ps <-> et ) ) $.
    mzpindd.5 $e |- ( x = ( f oF + g ) -> ( ps <-> ze ) ) $.
    mzpindd.6 $e |- ( x = ( f oF x. g ) -> ( ps <-> si ) ) $.
    mzpindd.7 $e |- ( x = A -> ( ps <-> rh ) ) $.
    $( "Structural" induction to prove properties of all polynomial
       functions. $)
    mzpindd $p |- ( ( ph /\ A e. ( mzPoly ` V ) ) -> rh ) $=
      ( va vb cmzp cfv wcel wa cz cmap co crab cvv elfvdm dmmzp syl6eleq adantl
      cdm cmzpcl cint wceq mzpval wss cv csn cxp wral cmpt caddc cof ssrab2 a1i
      cmul ovex vex zex constmap elrab sylanbrc ralrimiva adantr simpllr elmapg
      wf simpr biimpa syl21anc simplr ffvelrn syl2anc eqid fmptd sylibr adantlr
      elmap jca zaddcl simpl inidm off ad2ant2r 3expb zmulcl ex anbi12i 3imtr4g
      jca32 anbi1i ralrimivv wb rabex elmzpcl mpan2 mpbird intss1 eqsstrd an32s
      syl sselda mpdan simprbi ) AKNUHUIZUJZUKZKBJULULNUMUNZUMUNZUOZUJZIYGNUPUJ
      ZYKYFYLAYFNUHVAUPKNUHUQURUSUTAYLYFYKAYLUKZYEYJKYMYENVBUIZVCZYJYLYEYOVDANV
      EUTYMYJYNUJZYOYJVFYMYPYJYIVFZYHLVGZVHVIZYJUJZLULVJZMYHYRMVGZUIZVKZYJUJZLN
      VJZUKZYRUUBVLVMUNZYJUJZYRUUBVPVMUNZYJUJZUKZMYJVJLYJVJZUKUKZYMYQUUGUUMYQYM
      BJYIVNVOYMUUAUUFAUUAYLAYTLULAYRULUJZUKYSYIUJZCYTUUOUUPAYHYRULULNUMVQZLVRV
      SVTUTOBCJYSYISWAWBWCWDYMUUELNYMYRNUJZUKZUUDYIUJZDUUEUUSYHULUUDWGUUTUUSMYH
      UUCULUUDUUSUUBYHUJZUKZNULUUBWGZUURUUCULUJUVBULUPUJZYLUVAUVCUVDUVBVSVOAYLU
      URUVAWEUUSUVAWHUVDYLUKUVAUVCULNUUBUPUPWFWIWJYMUURUVAWKNULYRUUBWLWMUUDWNWO
      ULYHUUDVSUUQWRWPAUURDYLPWQBDJUUDYITWAWBWCWSAUUMYLAUULLMYJYJAYRYIUJZEUKZUU
      BYIUJZFUKZUKZUUHYIUJZGUKZUUJYIUJZHUKZUKZYRYJUJZUUBYJUJZUKUULAYHULYRWGZEUK
      ZYHULUUBWGZFUKZUKZYHULUUHWGZGUKZYHULUUJWGZHUKZUKZUVIUVNAUWAUWFAUWAUKZUWCU
      WDHUWGUWBGUWAUWBAUVQUVSUWBEFUVQUVSUKZUFUGYHYHYHVLULULULYRUUBUPUPUFVGZULUJ
      UGVGZULUJUKZUWIUWJVLUNULUJUWHUWIUWJWTUTUVQUVSXAZUVQUVSWHZYHUPUJUWHUUQVOZU
      WNYHXBZXCXDUTAUVRUVTGQXEWSUWAUWDAUVQUVSUWDEFUWHUFUGYHYHYHVPULULULYRUUBUPU
      PUWKUWIUWJVPUNULUJUWHUWIUWJXFUTUWLUWMUWNUWNUWOXCXDUTAUVRUVTHRXEXJXGUVFUVR
      UVHUVTUVEUVQEULYHYRVSUUQWRXKUVGUVSFULYHUUBVSUUQWRXKXHUVKUWCUVMUWEUVJUWBGU
      LYHUUHVSUUQWRXKUVLUWDHULYHUUJVSUUQWRXKXHXIUVOUVFUVPUVHBEJYRYIUAWABFJUUBYI
      UBWAXHUUIUVKUUKUVMBGJUUHYIUCWABHJUUJYIUDWAXHXIXLWDXJYLYPUUNXMZAYLYJUPUJUW
      PBJYIULYHUMVQXNMYJLMLLNXOXPUTXQYJYNXRYAXSYBXTYCYKKYIUJIBIJKYIUEWAYDYA $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d W a b c x y $.  $d F a b c x $.  $d V a b c x y $.  $d G a b c x $.

    $( Substituting polynomials for the variables of a polynomial results in a
       polynomial. ` G ` is expected to depend on ` y ` and provide the
       polynomials which are being substituted. $)
    mzpsubst $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ A. y e. V G e. (
        mzPoly ` W ) ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( y e. V |-> ( G ` x ) ) ) ) e. ( mzPoly `
        W ) ) $=
      ( va vb vc cvv wcel cfv cz cmpt wa wceq adantr mpteq2dva fveq1 eleq1d w3a
      cmzp wral cmap co cv simp1 cdm elfvdm dmmzp syl6eleq 3ad2ant2 simp3 simp2
      csn cxp caddc cof cmul simpr simpll3 simpll2 wf mzpf ffvelrn sylan expcom
      ralimdv imp eqid sylib wb zex elmapg sylancr mpbird syl21anc vex fvconst2
      fmpt syl mzpconstmpt 3ad2antl1 eqeltrd csb fvex fvmpt simplr ax-17 hbcsb1
      wel hbfv weq csbeq1a fveq1d cbvmpt fveq1i csbeq1 fvmptg sylancl eqtrd wfn
      syl5eq simpl3 ax17el hbel rcla4 sylc ffn 3syl dffn5v eqtr4d simp2l simp3l
      simp13 simp12 simplll simpllr ovex simplrl simplrr fnfvof syl22anc simp2r
      a1i simp3r mzpaddmpt syl2anc mzpmulmpt mzpindd syl31anc ) FJKZCEUBLKZDFUB
      LZKZBEUCZUAYLEJKZYPYMAMFUDUEZBEAUFZDLZNZCLZNZYNKZYLYMYPUGYMYLYQYPYMEUBUHJ
      CEUBUIUJUKULYLYMYPUMYLYMYPUNYLYQYPUAZAYRUUAGUFZLZNZYNKAYRUUAMEUDUEZHUFZUO
      UPZLZNZYNKAYRUUAIUUIUUJIUFZLZNZLZNZYNKAYRUUAUUJLZNZYNKZAYRUUAUUNLZNZYNKZA
      YRUUAUUJUUNUQURUEZLZNZYNKAYRUUAUUJUUNUSURUEZLZNZYNKUUDGCHIEUUEUUJMKZOZUUM
      AYRUUJNZYNUVLAYRUULUUJUVLYSYRKZOZUUAUUIKZUULUUJPUVOUVNYPYQUVPUVLUVNUTYLYQ
      YPUVKUVNVAYLYQYPUVKUVNVBUVNYPOZYQOZUVPEMUUAVCZUVQUVSYQUVQYTMKZBEUCZUVSUVN
      YPUWAUVNYOUVTBEYOUVNUVTYOYRMDVCUVNUVTDFVDYRMYSDVEVFVGVHZVIBEMYTUUAUUAVJVT
      ZVKQUVRMJKZYQUVPUVSVLZVMUVQYQUTMEUUAJJVNZVOVPZVQUUIUUJUUAHVRZVSWARYLYQUVK
      UVMYNKYPAUUJFWBWCWDUUEUUJEKZOZUURBUUJDWEZYNUWJUURAYRYSUWKLZNZUWKUWJAYRUUQ
      UWLUWJUVNOZUUQUUJUUALZUWLUWNUVPUUQUWOPUWNUVNYPYQUVPUWJUVNUTYLYQYPUWIUVNVA
      YLYQYPUWIUVNVBUWGVQIUUAUUOUWOUUIUUPUUJUUNUUASUUPVJUUJUUAWFWGWAUWNUWIUWLJK
      ZUWOUWLPUUEUWIUVNWHYSUWKWFUWIUWPOUWOUUJGEYSBUUFDWEZLZNZLUWLUUJUUAUWSBGIEY
      TUWRUUNYTKGWIBIYSUWQBIUUFDGVRIGWKBWIWJIAWKBWIWLBGWMYSDUWQBUUFDWNWOWPWQGUU
      JUWRUWLEJUWSGHWMZYSUWQUWKBUUFUUJDWRWOUWSVJWSXCWTXARUWJUWKYRXBZUWKUWMPUWJU
      WKYNKZYRMUWKVCUXAUWJUWIYPUXBUUEUWIUTYLYQYPUWIXDYOUXBBUUJEBGGUWKYNBGUUJDUW
      HGHBXEWJUUFYNKBWIXFBHWMDUWKYNBUUJDWNTXGXHZUWKFVDYRMUWKXIXJAYRUWKXKVKXLUXC
      WDUUEUUIMUUJVCZUVAOZUUIMUUNVCZUVDOZUAZUVGAYRUUSUVBUQUEZNZYNUXHUUJUUIXBZUU
      NUUIXBZYPYQUVGUXJPUXHUXDUXKUUEUXDUVAUXGXMUUIMUUJXIWAZUXHUXFUXLUUEUXEUXFUV
      DXNUUIMUUNXIWAZYLYQYPUXEUXGXOZYLYQYPUXEUXGXPZUXKUXLOZYPYQOZOZAYRUVFUXIUXS
      UVNOZUXKUXLUUIJKZUVPUVFUXIPUXKUXLUXRUVNXQZUXKUXLUXRUVNXRZUYAUXTMEUDXSYEZU
      XTUVPUVSUXTUWAUVSUXTUVNYPUWAUXSUVNUTUXQYPYQUVNXTUWBXHUWCVKUXTUWDYQUWEVMUX
      QYPYQUVNYAUWFVOVPZUUIUQUUJUUNJUUAYBYCRYCUXHUVAUVDUXJYNKUUEUXDUVAUXGYDZUUE
      UXEUXFUVDYFZAUUSUVBFYGYHWDUXHUVJAYRUUSUVBUSUEZNZYNUXHUXKUXLYPYQUVJUYIPUXM
      UXNUXOUXPUXSAYRUVIUYHUXTUXKUXLUYAUVPUVIUYHPUYBUYCUYDUYEUUIUSUUJUUNJUUAYBY
      CRYCUXHUVAUVDUYIYNKUYFUYGAUUSUVBFYIYHWDUUFUUKPZUUHUUMYNUYJAYRUUGUULUYJUUG
      UULPUVNUUAUUFUUKSQRTUUFUUPPZUUHUURYNUYKAYRUUGUUQUYKUUGUUQPUVNUUAUUFUUPSQR
      TUWTUUHUUTYNUWTAYRUUGUUSUWTUUGUUSPUVNUUAUUFUUJSQRTGIWMZUUHUVCYNUYLAYRUUGU
      VBUYLUUGUVBPUVNUUAUUFUUNSQRTUUFUVEPZUUHUVGYNUYMAYRUUGUVFUYMUUGUVFPUVNUUAU
      UFUVESQRTUUFUVHPZUUHUVJYNUYNAYRUUGUVIUYNUUGUVIPUVNUUAUUFUVHSQRTUUFCPZUUHU
      UCYNUYOAYRUUGUUBUYOUUGUUBPUVNUUAUUFCSQRTYJYK $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d W x a b $.  $d F x a b $.  $d R x a b $.  $d V a x $.

    $( Simplified version of ~ mzpsubst to simply relabel variables in a
       polynomial. $)
    mzprename $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ R : V --> W ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( x o. R ) ) ) e. ( mzPoly ` W ) ) $=
      ( va vb cvv wcel cmzp cfv wf cz cv cmpt wceq wa simplr syl2anc mpteq2dva
      w3a cmap co ccom simpr wb zex simpll elmapg sylancr mpbid fveq1 eqid fvex
      fcompt fvmpt syl eqcomd eqtrd fveq2d 3adant2 simp1 simp2 simpl1 3ad2antl3
      wral ffvelrn mzpproj ralrimiva mzpsubst syl3anc eqeltrd ) EHIZCDJKIZDEBLZ
      UAZAMEUBUCZANZBUDZCKZOZAVQFDVRGVQFNZBKZGNZKZOZKZOZCKZOZEJKZVMVOWAWJPVNVMV
      OQZAVQVTWIWLVRVQIZQZVSWHCWNVSFDWCVRKZOZWHWNEMVRLZVOVSWPPWNWMWQWLWMUEWNMHI
      VMWMWQUFUGVMVOWMUHMEVRHHUIUJUKVMVOWMRFVRBDEMUOSWNFDWOWGWNWBDIZQZWGWOWSWMW
      GWOPWLWMWRRGVRWEWOVQWFWCWDVRULWFUMWCVRUNUPUQURTUSUTTVAVPVMVNWFWKIZFDVFWJW
      KIVMVNVOVBVMVNVOVCVPWTFDVPWRQVMWCEIZWTVMVNVOWRVDVOVMWRXAVNDEWBBVGVEGEWCVH
      SVIAFCWFDEVJVKVL $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d W x $.  $d F x $.  $d V x $.
    $( A polynomial is a polynomial over all larger index sets. $)
    mzpresrename $p |- ( ( W e. _V /\ V C_ W /\ F e. ( mzPoly ` V ) ) -> ( x e.
        ( ZZ ^m W ) |-> ( F ` ( x |` V ) ) ) e. ( mzPoly ` W ) ) $=
      ( cvv wcel wss cmzp cfv w3a cz cmap co cv cres cmpt cid ccom wf mpan wrel
      wa wceq wb zex elmapg biimpa 3ad2antl1 frel coires1 3syl eqcomd mpteq2dva
      fveq2d simp1 simp3 wf1o f1oi ax-mp fss 3ad2ant2 mzprename syl3anc eqeltrd
      f1of ) DEFZCDGZBCHIFZJZAKDLMZANZCOZBIZPAVJVKQCOZRZBIZPZDHIZVIAVJVMVPVIVKV
      JFZUBZVLVOBVTVOVLVTDKVKSZVKUAVOVLUCVFVGVSWAVHVFVSWAKEFVFVSWAUDUEKDVKEEUFT
      UGUHDKVKUIVKCUJUKULUNUMVIVFVHCDVNSZVQVRFVFVGVHUOVFVGVHUPVGVFWBVHCCVNSZVGW
      BCCVNUQWCCURCCVNVEUSCCDVNUTTVAAVNBCDVBVCVD $.
      $( [5-Oct-2014] $)
  $}


  ${
    $d A a b d e f g h i j k l $.  $d B a b c d e f g h i j k l $.
    mzpcompact2lem.i $e |- B e. _V $.
    $( Lemma for ~ mzpcompact2 . $)
    mzpcompact2lem $p |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly
        ` a ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) )
        $=
      ( vd cmzp cfv wcel cz co cmpt wceq wa wrex cfn c0 mpteq2dva anbi2d ve wss
      vf vg vh vi vj vk vl cv cmap cres wtru tru csn cxp caddc cof cmul cvv 0ex
      0fin mzpconst 0ss a1i simpr elmapssres syl3anc vex fvconst2 syl fconstmpt
      syl6reqr fveq1 adantr eqeq2d rcla4ev syl12anc fveq2 reseq2 fveq2d anbi12d
      mpan sseq1 rexeqbidv sylancr adantl snfi snex mzpproj mp2an snssi cbvmptv
      snid simpl snssd eqid fvex fvmpt fvres ax-mp syl6req syl5eq wf w3a wi cun
      simplll simprll unfi syl2anc ssun1 simpllr mzpresrename simprlr mzpaddmpt
      unex ssun2 simplr wfn ovex mzpf ffn 3syl ofmpteq zex elmap reseq1 oveq12d
      resabs1 fveq2i oveq12i eqtrd eqeq1d rexbidv eqeq1 2rexbidv cbvrexv syl6bb
      weq simprr unssd biimpi fssres syl2anr sylibr mzpmulmpt adantlrr adantrrr
      simplrr simprrr mpbird r19.40 rexlimdvv ex rexlimivv imp ad2ant2l 3adant1
      exp32 simpld simprd mzpindd eqeq2i anbi2i 2rexbii sylib ) ABHIZJZCUJZBUBZ
      AGKBUKLZGUJZUVJULZDUJZIZMZNZOZDUVJHIZPCQPZUVKAEUVLEUJZUVJULZUVOIZMZNZOZDU
      VTPCQPUMUVIUWAUNUMUVKUAUJZUVQNZOZDUVTPCQPZUVKUVLUCUJZUOZUPZUVQNZOZDUVTPZC
      QPZUVKUDUVLUWLUDUJZIZMZUVQNZOZDUVTPZCQPZUEUJZBUBZUWLGUVLUVMUXFULZUFUJZIZM
      ZNZOZUFUXFHIZPZUEQPZUGUJZBUBZUWSGUVLUVMUXQULZUHUJZIZMZNZOZUHUXQHIZPZUGQPZ
      UVKUWLUWSUQURZLZUVQNZOZDUVTPZCQPZUVKUWLUWSUSURZLZUVQNZOZDUVTPZCQPZUWAUAAU
      CUDBUWLKJZUWRUMUYTRQJRBUBZUWNGUVLUVMRULZUVOIZMZNZOZDRHIZPZUWRVBUYTKRUKLZU
      WMUPZVUGJZVUAUWNGUVLVUBVUJIZMZNZVUHRUTJUYTVUKVAUWLRVCWCVUAUYTBVDZVEUYTVUM
      GUVLUWLMUWNUYTGUVLVULUWLUYTUVMUVLJZOZVUBVUIJZVULUWLNVUQVUPVUABUTJZVURUYTV
      UPVFVUAVUQVUOVEVUSVUQFVEUVMKBRVGVHVUIUWLVUBUCVIZVJVKSGUVLUWLVLVMVUFVUAVUN
      ODVUJVUGUVOVUJNZVUEVUNVUAVVAVUDVUMUWNVVAGUVLVUCVULVVAVUCVULNVUPVUBUVOVUJV
      NVOSVPTVQVRUWQVUHCRQUVJRNZUWPVUFDUVTVUGUVJRHVSVVBUVKVUAUWOVUEUVJRBWDVVBUV
      QVUDUWNVVBGUVLUVPVUCVVBUVPVUCNVUPVVBUVNVUBUVOUVJRUVMVTWAVOSVPWBWEVQWFWGUW
      LBJZUXEUMVVCUWMQJUWMBUBZUXAGUVLUVMUWMULZUVOIZMZNZOZDUWMHIZPZUXEUWLWHVVCUD
      KUWMUKLZUWTMZVVJJZVVDUXAGUVLVVEVVMIZMZNZVVKVVNVVCUWMUTJUWLUWMJZVVNUWLWIUW
      LVUTWNZUDUWMUWLWJWKVEUWLBWLVVCUXAGUVLUWLUVMIZMVVPUDGUVLUWTVVTUWLUWSUVMVNW
      MVVCGUVLVVTVVOVVCVUPOZVVOUWLVVEIZVVTVWAVVEVVLJZVVOVWBNVWAVUPVVDVUSVWCVVCV
      UPVFVWAUWLBVVCVUPWOWPVUSVWAFVEUVMKBUWMVGVHUDVVEUWTVWBVVLVVMUWLUWSVVEVNVVM
      WQUWLVVEWRWSVKVVRVWBVVTNVVSUWLUWMUVMWTXAXBSXCVVIVVDVVQODVVMVVJUVOVVMNZVVH
      VVQVVDVWDVVGVVPUXAVWDGUVLVVFVVOVWDVVFVVONVUPVVEUVOVVMVNVOSVPTVQVRUXDVVKCU
      WMQUVJUWMNZUXCVVIDUVTVVJUVJUWMHVSVWEUVKVVDUXBVVHUVJUWMBWDVWEUVQVVGUXAVWEG
      UVLUVPVVFVWEUVPVVFNVUPVWEUVNVVEUVOUVJUWMUVMVTWAVOSVPWBWEVQWFWGUMUVLKUWLXD
      ZUXPOZUVLKUWSXDZUYGOZXEZUYMUYSVWGVWIUYMUYSOZUMUXPUYGVWKVWFVWHUXPUYGVWKUXM
      UYGVWKXFZUEUFQUXNUXFQJZUXIUXNJZOZUXMVWLVWOUXMOZUYDVWKUGUHQUYEVWPUXQQJZUXT
      UYEJZOZUYDVWKVWPVWSUYDOZOZUYLUYROZCQPZVWKVXAVXCUVKUXKUYBUYHLZUVQNZOZDUVTP
      ZUVKUXKUYBUYNLZUVQNZOZDUVTPZOZCQPZVWPVWSUXRVXMUYCVWOUXGVWSUXROZVXMUXLVWOU
      XGOZVXNOZUXFUXQXGZQJZVXQBUBZVXDGUVLUVMVXQULZUVOIZMZNZOZDVXQHIZPZVXSVXHVYB
      NZOZDVYEPZVXMVXPVWMVWQVXRVWMVWNUXGVXNXHVXOVWQVWRUXRXIUXFUXQXJXKVXPUIKVXQU
      KLZUIUJZUXFULZUXIIZVYKUXQULZUXTIZUQLZMZVYEJZVXSVXDGUVLVXTVYQIZMZNZVYFVXPU
      IVYJVYMMVYEJZUIVYJVYOMVYEJZVYRVXPVXQUTJZUXFVXQUBZVWNWUBWUDVXPUXFUXQUEVIUG
      VIXQZVEZWUEVXPUXFUXQXLZVEVWMVWNUXGVXNXMZUIUXIUXFVXQXNVHZVXPWUDUXQVXQUBZVW
      RWUCWUGWUKVXPUXQUXFXRZVEVXOVWQVWRUXRXOZUIUXTUXQVXQXNVHZUIVYMVYOVXQXPXKVXP
      UXFUXQBVWOUXGVXNXSZVXOVWSUXRUUAZUUBZVXPVXDGUVLUXJUYAUQLZMZVYTVXPUVLUTJZUX
      KUVLXTZUYBUVLXTZVXDWUSNWUTVXPKBUKYAVEZVXPUXKUVHJZUVLKUXKXDWVAVXPVUSUXGVWN
      WVDVUSVXPFVEZWUOWUIGUXIUXFBXNVHUXKBYBUVLKUXKYCYDZVXPUYBUVHJZUVLKUYBXDWVBV
      XPVUSUXRVWRWVGWVEWUPWUMGUXTUXQBXNVHUYBBYBUVLKUYBYCYDZGUVLUXJUYAUQUTYEVHVX
      PGUVLWURVYSVXPVUPOZVYSVXTUXFULZUXIIZVXTUXQULZUXTIZUQLZWURWVIVXTVYJJZVYSWV
      NNWVIVXQKVXTXDZWVOVUPBKUVMXDZVXSWVPVXPVUPWVQKBUVMYFFYGUUCWUQBKVXQUVMUUDUU
      EKVXQVXTYFWUFYGUUFZUIVXTVYPWVNVYJVYQVYKVXTNZVYMWVKVYOWVMUQWVSVYLWVJUXIVYK
      VXTUXFYHWAZWVSVYNWVLUXTVYKVXTUXQYHWAZYIVYQWQWVKWVMUQYAWSVKWVKUXJWVMUYAUQW
      VJUXHUXIWUEWVJUXHNWUHUVMUXFVXQYJXAYKZWVLUXSUXTWUKWVLUXSNWULUVMUXQVXQYJXAY
      KZYLXBSYMVYDVXSWUAODVYQVYEUVOVYQNZVYCWUAVXSWWDVYBVYTVXDWWDGUVLVYAVYSWWDVY
      AVYSNVUPVXTUVOVYQVNVOSVPTVQVRVXPUIVYJVYMVYOUSLZMZVYEJZVXSVXHGUVLVXTWWFIZM
      ZNZVYIVXPWUBWUCWWGWUJWUNUIVYMVYOVXQUUGXKWUQVXPVXHGUVLUXJUYAUSLZMZWWIVXPWU
      TWVAWVBVXHWWLNWVCWVFWVHGUVLUXJUYAUSUTYEVHVXPGUVLWWKWWHWVIWWHWVKWVMUSLZWWK
      WVIWVOWWHWWMNWVRUIVXTWWEWWMVYJWWFWVSVYMWVKVYOWVMUSWVTWWAYIWWFWQWVKWVMUSYA
      WSVKWVKUXJWVMUYAUSWWBWWCYLXBSYMVYHVXSWWJODWWFVYEUVOWWFNZVYGWWJVXSWWNVYBWW
      IVXHWWNGUVLVYAWWHWWNVYAWWHNVUPVXTUVOWWFVNVOSVPTVQVRVXLVYFVYIOCVXQQUVJVXQN
      ZVXGVYFVXKVYIWWOVXFVYDDUVTVYEUVJVXQHVSZWWOUVKVXSVXEVYCUVJVXQBWDZWWOUVQVYB
      VXDWWOGUVLUVPVYAWWOUVPVYANVUPWWOUVNVXTUVOUVJVXQUVMVTWAVOSZVPWBWEWWOVXJVYH
      DUVTVYEWWPWWOUVKVXSVXIVYGWWQWWOUVQVYBVXHWWRVPWBWEWBVQVRUUHUUIVXAVXBVXLCQV
      XAUYLVXGUYRVXKVXAUYKVXFDUVTVXAUYJVXEUVKVXAUYIVXDUVQVXAUWLUXKUWSUYBUYHVWOU
      XGUXLVWTUUJZVWPVWSUXRUYCUUKZYIYNTYOVXAUYQVXJDUVTVXAUYPVXIUVKVXAUYOVXHUVQV
      XAUWLUXKUWSUYBUYNWWSWWTYIYNTYOWBYOUULUYLUYRCQUUMVKUUTUUNUUOUUPUUQUURUUSZU
      VAVWJUYMUYSWXAUVBUWHUWNNZUWJUWPCDQUVTWXBUWIUWOUVKUWHUWNUVQYPTYQUWHUXANZUW
      JUXCCDQUVTWXCUWIUXBUVKUWHUXAUVQYPTYQUAUCYTZUWKUVKUWLUVQNZOZDUVTPZCQPUXPWX
      DUWJWXFCDQUVTWXDUWIWXEUVKUWHUWLUVQYPTYQWXGUXOCUEQCUEYTZWXGUXGUWLGUVLUXHUV
      OIZMZNZOZDUXNPUXOWXHWXFWXLDUVTUXNUVJUXFHVSWXHUVKUXGWXEWXKUVJUXFBWDWXHUVQW
      XJUWLWXHGUVLUVPWXIWXHUVPWXINVUPWXHUVNUXHUVOUVJUXFUVMVTWAVOSVPWBWEWXLUXMDU
      FUXNDUFYTZWXKUXLUXGWXMWXJUXKUWLWXMGUVLWXIUXJWXMWXIUXJNVUPUXHUVOUXIVNVOSVP
      TYRYSYRYSUAUDYTZUWKUVKUWSUVQNZOZDUVTPZCQPUYGWXNUWJWXPCDQUVTWXNUWIWXOUVKUW
      HUWSUVQYPTYQWXQUYFCUGQCUGYTZWXQUXRUWSGUVLUXSUVOIZMZNZOZDUYEPUYFWXRWXPWYBD
      UVTUYEUVJUXQHVSWXRUVKUXRWXOWYAUVJUXQBWDWXRUVQWXTUWSWXRGUVLUVPWXSWXRUVPWXS
      NVUPWXRUVNUXSUVOUVJUXQUVMVTWAVOSVPWBWEWYBUYDDUHUYEDUHYTZWYAUYCUXRWYCWXTUY
      BUWSWYCGUVLWXSUYAWYCWXSUYANVUPUXSUVOUXTVNVOSVPTYRYSYRYSUWHUYINZUWJUYKCDQU
      VTWYDUWIUYJUVKUWHUYIUVQYPTYQUWHUYONZUWJUYQCDQUVTWYEUWIUYPUVKUWHUYOUVQYPTY
      QUWHANZUWJUVSCDQUVTWYFUWIUVRUVKUWHAUVQYPTYQUVCWCUVSUWGCDQUVTUVRUWFUVKUVQU
      WEAGEUVLUVPUWDGEYTUVNUWCUVOUVMUWBUVJYHWAWMUVDUVEUVFUVG $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b d $.  $d B a b c d $.
    $( Polynomials are finitary objects and can only reference a finite number
       of variables, even if the index set is infinite.  Thus, every polynomial
       can be expressed as a (uniquely minimal, although we do not prove that)
       polynomial on a finite number of variables, which is then extended by
       adding an arbitrary set of ignored variables. $)
    mzpcompact2 $p |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly ` a
        ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) ) $=
      ( vd cmzp cfv wcel cv wss cz cmap co cmpt wceq wa wrex cfn cvv cdm elfvdm
      cres wi dmmzp syl6eleq fveq2 eleq2d sseq2 oveq2 mpteq1 syl eqeq2d anbi12d
      2rexbidv imbi12d vex mzpcompact2lem vtoclg pm2.43i ) ABGHZIZCJZBKZAELBMNZ
      EJVCUCDJHZOZPZQZDVCGHZRCSRZVBBTIVBVKUDZVBBGUATABGUBUEUFAFJZGHZIZVCVMKZAEL
      VMMNZVFOZPZQZDVJRCSRZUDVLFBTVMBPZVOVBWAVKWBVNVAAVMBGUGUHWBVTVICDSVJWBVPVD
      VSVHVMBVCUIWBVRVGAWBVQVEPVRVGPVMBLMUJEVQVEVFUKULUMUNUOUPAVMCDEFUQURUSULUT
      $.
      $( [9-Oct-2014] $)
  $}
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Miscellanea for Diophantine sets 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Two real numbers are equal to 0 iff their Euclidean norm is.  Closed
     theorem of ~ sumsqeq0 . $)
  sumsqeq0 $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A = 0 /\ B = 0 ) <-> ( ( A ^ 2
      ) + ( B ^ 2 ) ) = 0 ) ) $=
    ( cr wcel wa cc0 wceq c2 cexp co caddc wne wo wb neeq1 oveq1 neeq1d bibi12d
    cif 0re wn neorian orbi1d oveq1d orbi2d oveq2d sumsqne0i dedth2h necon4bbid
    elimel syl5bbr ) ACDZBCDZEZAFGBFGEZAHIJZBHIJZKJZFUOUAAFLZBFLZMZUNURFLZAFBFU
    BULUMVAVBNULAFSZFLZUTMZVCHIJZUQKJZFLZNVDUMBFSZFLZMZVFVIHIJZKJZFLZNABFFAVCGZ
    VAVEVBVHVOUSVDUTAVCFOUCVOURVGFVOUPVFUQKAVCHIPUDQRBVIGZVEVKVHVNVPUTVJVDBVIFO
    UEVPVGVMFVPUQVLVFKBVIHIPUFQRVCVIAFCTUJBFCTUJUGUHUKUI $.
    $( [5-Oct-2014] $)


  $( A composition of two relations is empty iff there is no overlap betwen the
     range of the second and the domain of the first.  Useful in combination
     with ~ coundi and ~ coundir to prune meaningless terms in the result. $)
  coeq0 $p |- ( ( A o. B ) = (/) <-> ( dom A i^i ran B ) = (/) ) $=
    ( ccom c0 wceq crn cres cdm wrel wb relco relrn0 ax-mp eqeq1i relres reldm0
    cin rnco dmres incom eqtri 3bitr3i 3bitri ) ABCZDEZUDFZDEZABFZGZFZDEZAHZUHQ
    ZDEZUDIUEUGJABKUDLMUFUJDABRNUIDEZUIHZDEZUKUNUIIZUOUQJAUHOZUIPMURUOUKJUSUILM
    UPUMDUPUHULQUMAUHSUHULTUANUBUC $.
    $( [8-Oct-2014] $)

  $( ~ coeq0 but without explicitly introducing domain and range symbols. $)
  coeq0i $p |- ( ( A : C --> D /\ B : E --> F /\ ( C i^i F ) = (/) ) ->
      ( A o. B ) = (/) ) $=
    ( wf cin c0 wceq w3a cdm crn ccom wss frn 3ad2ant2 sslin syl fdm ineq1d ss0
    3ad2ant1 simp3 eqtrd sseqtrd coeq0 sylibr ) CDAGZEFBGZCFHZIJZKZALZBMZHZIJZA
    BNIJUMUPIOUQUMUPUNFHZIUMUOFOZUPUROUJUIUSULEFBPQUOFUNRSUMURUKIUMUNCFUIUJUNCJ
    ULCDATUCUAUIUJULUDUEUFUPUBSABUGUH $.
    $( [16-Oct-2014] $)

  $( Split a finite 1-based set of integers in the middle, allowing either end
     to be empty ( ` ( 1 ... 0 ) ` ). $)
  fzsplit1nn0 $p |- ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) -> ( 1 ... B ) = ( ( 1
      ... A ) u. ( ( A + 1 ) ... B ) ) ) $=
    ( cn0 wcel cle wbr c1 cfz co caddc cun wceq cn cc0 wo wa cz adantr syl6eq
    c0 wi elnn0 simprl wb nnz 1z a1i nn0z ad2antrl elfz syl3anc nnge1 mpbir2and
    simprr fzsplit syl2anc uncom oveq1 ax-1cn addid2i oveq1d oveq2 fz10 uneq12d
    un0 syl5req jaoian ex sylbi 3impib ) ACDZBCDZABEFZGBHIZGAHIZAGJIZBHIZKZLZVK
    AMDZANLZOZVLVMPZVSUAAUBWBWCVSVTWCVSWAVTWCPZVLAVNDZVSVTVLVMUCWDWEGAEFZVMWDAQ
    DZGQDZBQDZWEWFVMPUDVTWGWCAUERWHWDUFUGVLWIVTVMBUHUIAGBUJUKVTWFWCAULRVTVLVMUN
    UMCAGBUOUPWAWCPZVRVQVOKZVNVOVQUQWJWKVNTKVNWJVQVNVOTWJVPGBHWJVPNGJIZGWAVPWLL
    WCANGJURRGUSUTSVAWJVOGNHIZTWAVOWMLWCANGHVBRVCSVDVNVESVFVGVHVIVJ $.
    $( [8-Oct-2014] $)

  ${
    $d A c f a $.  $d B c f a $.
    $( An infinite set contains subsets equinumerous to every finite set.
       Extension of ~ isinf from finite ordinals to all finite sets. $)
    isinffi $p |- ( ( -. A e. Fin /\ B e. Fin ) -> E. f f : B -1-1-> A ) $=
      ( vc va cfn wcel wn wa cv wss cen wbr wex wf1 com ad2antlr syl2anc mpd ex
      ccrd cfv wral ficardom isinf wceq breq2 anbi2d exbidv rcla4va wf1o simprr
      syl2anr ficardid entr wi ensymg vex bren sylib adantl simplrl f1ss eximdv
      f1of1 exlimdv ) AFGHZBFGZIZDJZAKZVJBUAUBZLMZIZDNZBACJZOZCNZVHVLPGVKVJEJZL
      MZIZDNZEPUCVOVGBUDDAEUEWBVOEVLPVSVLUFZWAVNDWCVTVMVKVSVLVJLUGUHUIUJUMVIVNV
      RDVIVNVRVIVNIZBVJVPUKZCNZVRWDBVJLMZWFWDVJBLMZWGWDVMVLBLMZWHVIVKVMULVHWIVG
      VNBUNQVJVLBUORVHWHWGUPVGVNVJBFUQQSBVJCDURUSUTWDWEVQCWDWEVQWDWEIBVJVPOZVKV
      QWEWJWDBVJVPVEVAVIVKVMWEVBBVJAVPVCRTVDSTVFS $.
      $( [8-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 1: definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Dioph $.
  $( Extend class notation to include the family of Diophantine sets. $)
  cdioph $a class Dioph $.

  ${
    $d n d k p t u $.
    $( A Diophantine set is a set of natural numbers which is a projection of
       the zero set of some polynomial.  This definition somewhat awkwardly
       mixes ` ZZ ` (via ` mzPoly ` ) and ` NN0 ` (to define the zero sets);
       the former could be avoided by considering coincidence sets of ` NN0 `
       polynomials at the cost of requiring two, and the second is driven by
       consistency with our mu-recursive functions and the requirements of the
       DPRM proof.  Both are avoidable at a complexity cost.  In particular, it
       is a consequence of ~ 4sq that implicitly restricting variables to
       ` NN0 ` adds no expressive power over allowing them to range over
       ` ZZ ` .  While this definition stipulates a specific index set for the
       polynomials, there is actually flexibility here, see ~ eldioph2b . $)
    df-dioph $a |- Dioph = ( n e. NN0 |-> { d | E. k e. ( ZZ>= ` n ) E. p e. (
        mzPoly ` ( 1 ... k ) ) d = { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t =
        ( u |` ( 1 ... n ) ) /\ ( p ` u ) = 0 ) } } ) $.
  $}

  ${
    $d D n d k p $.  $d N n d k p t u $.
    $( Initial expression of Diophantine property of a set. $)
    eldiophb $p |- ( D e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. k e. ( ZZ>= ` N )
        E. p e. (
        mzPoly ` ( 1 ... k ) ) D = { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t =
        ( u |` ( 1 ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( vn vd cdioph cfv wcel cn0 cv c1 cfz co wceq wrex cab cuz cres cmap cmzp
      cc0 cdm df-dioph dmmptss elfvdm sseldi fveq2 oveq2 reseq2d eqeq2d rexbidv
      wa anbi1d abbidv rexeqbidv fvex ab2rexex fvmpt eleq2d cvv wi ovex abrexex
      simpl reximi ss2abi ssexi eleq1a ax-mp rexlimivw 2rexbidv syl6bb biadan2
      eqeq1 elab3 ) CEIJZKZELKZCBMZAMZNEOPZUAZQZWCFMJUDQZUOZALNDMOPZUBPZRZBSZQZ
      FWIUCJZRZDETJZRZVTIUELEGLHMZWBWCNGMZOPZUAZQZWGUOZAWJRZBSZQZFWNRZDWSTJZRZH
      SZIABDGFHUFZUGCEIUHUIWAVTCWRWLQZFWNRZDWPRZHSZKWQWAVSXOCGEXJXOLIWSEQZXIXNH
      XPXGXMDXHWPWSETUJXPXFXLFWNXPXEWLWRXPXDWKBXPXCWHAWJXPXBWFWGXPXAWEWBXPWTWDW
      CWSENOUKULUMUPUNUQUMUNURUQXKDFHWPWNWLETUSWIUCUSUTVAVBXNWQHCWOCVCKZDWPWMXQ
      FWNWLVCKWMXQVDWLWFAWJRZBSABWJWELWIUBVEVFWKXRBWHWFAWJWFWGVGVHVIVJWLVCCVKVL
      VMVMWRCQXLWMDFWPWNWRCWLVQVNVRVOVP $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d N k p t u $.  $d K k p t u $.  $d P k p t u $.
    $( Condition for a set to be Diophantine (unpacking existential
       quantifier) $)
    eldioph $p |- ( ( N e. NN0 /\ K e. ( ZZ>= ` N ) /\ P e. ( mzPoly ` ( 1 ...
        K ) ) ) ->
        { t | E. u e. ( NN0 ^m ( 1 ... K ) ) ( t = ( u |` ( 1 ... N ) ) /\ ( P
        ` u ) = 0 ) } e. ( Dioph ` N ) ) $=
      ( vp vk cn0 wcel cfv c1 cfz co cmzp cv wceq cc0 cmap wrex cab cuz cres wa
      cdioph simp1 simp2 simp3 eqidd fveq1 eqeq1d anbi2d rexbidv abbidv rcla4ev
      eqeq2d syl2anc oveq2 fveq2d oveq2d rexeqdv rexeqbidv eldiophb sylanbrc
      w3a ) EHIZDEUAJZIZCKDLMZNJZIZVDZVEBOAOZKELMUBPZVLCJZQPZUCZAHVHRMZSZBTZVMV
      LFOZJZQPZUCZAHKGOZLMZRMZSZBTZPZFWENJZSZGVFSZVSEUDJIVEVGVJUEVKVGVSWCAVQSZB
      TZPZFVISZWLVEVGVJUFVKVJVSVSPZWPVEVGVJUGVKVSUHWOWQFCVIVTCPZWNVSVSWRWMVRBWR
      WCVPAVQWRWBVOVMWRWAVNQVLVTCUIUJUKULUMUOUNUPWKWPGDVFWDDPZWIWOFWJVIWSWEVHNW
      DDKLUQZURWSWHWNVSWSWGWMBWSWCAWFVQWSWEVHHRWTUSUTUMUOVAUNUPABVSGEFVBVC $.
      $( [5-Oct-2014] $)
  $}

  $(
  $d A f $.
  fifzf1o $p |- ( A e. Fin -> ( ( # ` A ) e. NN0 /\ E. f f : ( 1 ... ( # ` A ) ) -1-1-onto-> A ) ) $=
      ? $.
  $)

  $(
      eldioph2r: single rename with an injection function from a finite set of witnesses to an infinite set.  original polynomial has the SMALLER variable set
      eldioph2: *reverse* rename.  use mzpcompact2 to show that the original polynomial is a renaming, and is thus generates the same Diophantine set as a finitary polynomial
  $)

  ${
    $d S a b c d $.  $d T a b c d $.  $d M a b c d $.  $d O a b c d $.
    $d P b c d $.
    $( Renaming and adding unused witness variables does not change the
       Diophantine set coded by a polynomial. $)
    diophrw $p |- ( ( S e. _V /\ M : T -1-1-> S /\ ( M |` O ) = ( _I |` O ) )
        -> { a | E. b e. ( NN0 ^m S ) ( a = ( b |` O ) /\ ( ( d e. ( ZZ ^m S )
        |-> ( P ` ( d o. M ) ) ) ` b ) = 0 ) } = { a | E. c e. ( NN0 ^m T ) ( a
        = ( c |` O ) /\ ( P ` c ) = 0 ) } ) $=
      ( cvv wcel cres wceq cz ccom cc0 cn0 wf a1i c0 wf1 cid w3a cv cmap co cfv
      cmpt wa wrex simpr nn0ex simp1 adantr elmapg sylancr mpbid simp2 ad2antrr
      f1f syl fco syl2anc f1dmex mpbird simprl resco simpll3 coeq2d wrel simplr
      wb frel coires1 3syl 3eqtrd eqtr4d wss simpll1 oveq2 sseq12d nn0ssz mapss
      zex ax-mp vtoclg sseldd coeq1 fveq2d eqid fvex fvmpt simprr eqtr3d reseq1
      vex weq eqeq2d eqeq1d anbi12d rcla4ev syl12anc ex rexlimdva ccnv crn cdif
      fveq2 csn cxp cun cin wf1o f1cnv 0z elexi fconst disjdif fun syl21anc frn
      f1of undif sylib 0nn0 snssi ssequn2 mpbi feq23d resundir simpl3 cima wfun
      cnveqd simpl2 eqtrd cdm syl5eq uneq12d un0 df-f1 simprbi funcnvres df-ima
      rneqd rnresi reseq2d cnvresid 3eqtr3d dmres snnz dmxp ineq2i inss1 eqtr2d
      wne rnss eqsstrd syl5ss inssdif0 relres reldm0 sylibr 3eqtrrd fss sylancl
      resss coundir coass f1cocnv1 ineq1i incom 3eqtri coeq0 mpbir fcoi1 impbid
      abbidv ) BJKZCBDUAZDELZUBELZMZUCZFUDZGUDZELZMZUWFINBUEUFZIUDZDOZAUGZUHZUG
      ZPMZUIZGQBUEUFZUJZUWEHUDZELZMZUWSAUGZPMZUIZHQCUEUFZUJZFUWDUWRUXFUWDUWPUXF
      GUWQUWDUWFUWQKZUIZUWPUXFUXHUWPUIZUWFDOZUXEKZUWEUXJELZMZUXJAUGZPMZUXFUXIUX
      KCQUXJRZUXIBQUWFRZCBDRZUXPUXHUXQUWPUXHUXGUXQUWDUXGUKUXHQJKZUVSUXGUXQVLZUL
      UWDUVSUXGUVSUVTUWCUMZUNQBUWFJJUOZUPUQUNUWDUXRUXGUWPUWDUVTUXRUVSUVTUWCURZC
      BDUTZVAUSCBQUWFDVBVCUXIUXSCJKZUXKUXPVLULUWDUYEUXGUWPUWDUVTUVSUYEUYCUYACBJ
      DVDVCZUSQCUXJJJUOUPVEUXIUWEUWGUXLUXHUWHUWOVFUXIUXLUWFUWAOZUWFUWBOZUWGUXLU
      YGMUXIUWFDEVGSUXIUWAUWBUWFUVSUVTUWCUXGUWPVHVIUXIUXQUWFVJUYHUWGMUXIUXGUXQU
      WDUXGUWPVKZUXIUXSUVSUXTULUWDUVSUXGUWPUYAUSUYBUPUQBQUWFVMUWFEVNVOVPVQUXIUW
      NUXNPUXIUWFUWIKUWNUXNMUXIUWQUWIUWFUXIUVSUWQUWIVRZUVSUVTUWCUXGUWPVSQUWEUEU
      FZNUWEUEUFZVRZUYJFBJUWEBMUYKUWQUYLUWIUWEBQUEVTUWEBNUEVTWAQNVRZUYMWBQNUWEW
      DFWPWCWEWFVAUYIWGIUWFUWLUXNUWIUWMIGWQUWKUXJAUWJUWFDWHWIUWMWJZUXJAWKWLVAUX
      HUWHUWOWMWNUXDUXMUXOUIHUXJUXEUWSUXJMZUXAUXMUXCUXOUYPUWTUXLUWEUWSUXJEWOWRU
      YPUXBUXNPUWSUXJAXHWSWTXAXBXCXDUWDUXDUWRHUXEUWDUWSUXEKZUIZUXDUWRUYRUXDUIZU
      WSDXEZOZBDXFZXGZPXIZXJZXKZUWQKZUWEVUFELZMZVUFUWMUGZPMZUWRUYSVUGBQVUFRZUYS
      VUBVUCXKZQVUDXKZVUFRZVULUYSVUBQVUARZVUCVUDVUERZVUBVUCXLZTMZVUOUYSCQUWSRZV
      UBCUYTRZVUPUYRVUTUXDUYRUYQVUTUWDUYQUKUYRUXSUYEUYQVUTVLULUWDUYEUYQUYFUNQCU
      WSJJUOUPUQZUNZUYSUVTVUBCUYTXMVVAUWDUVTUYQUXDUYCUSZCBDXNVUBCUYTYBVOZVUBCQU
      WSUYTVBVCVUQUYSVUCPPJPNXOXPXPZXQSZVUSUYSVUBBXRZSZVUBVUCQVUDVUAVUEXSXTUYSV
      UMVUNBQVUFUYSVUBBVRZVUMBMUWDVVJUYQUXDUWDUVTUXRVVJUYCUYDCBDYAVOUSVUBBYCYDZ
      VUNQMZUYSVUDQVRZVVLPQKVVMYEPQYFWEVUDQYGYHSYIUQUWDVUGVULVLZUYQUXDUWDUXSUVS
      VVNULUYAQBVUFJJUOUPUSVEUYSUWEUWTVUHUYRUXAUXCVFUYRUWTVUHMUXDUYRVUHVUAELZVU
      EELZXKZUWTTXKZUWTVUHVVQMUYRVUAVUEEYJSUYRVVOUWTVVPTUYRVVOUWSUYTELZOZUWSUWB
      OZUWTVVOVVTMUYRUWSUYTEVGSUYRVVSUWBUWSUYRUWAXEZUWBXEZVVSUWBUYRUWAUWBUVSUVT
      UWCUYQYKZYNUYRVWBUYTDEYLZLZVVSUYRUVTUYTYMZVWBVWFMUVSUVTUWCUYQYOUVTUXRVWGC
      BDUUAUUBEDUUCVOUYRVWEEUYTUYRVWEUWAXFZUWBXFZEVWEVWHMUYRDEUUDSUYRUWAUWBVWDU
      UEZVWIEMUYREUUFSZVPUUGYPVWCUWBMUYREUUHSUUIVIUYRVUTUWSVJVWAUWTMVVBCQUWSVMU
      WSEVNVOVPUYRVVPYQZTMZVVPTMZUYRVWLEVUEYQZXLZTVUEEUUJUYRVWPEVUCXLZTVWOVUCEV
      UDTUUPVWOVUCMPVVFUUKVUCVUDUULWEZUUMUYREBXLZVUBVRVWQTMUYRVWSEVUBEBUUNUYREV
      WHVUBUYRVWHVWIEVWJVWKUUOUYRUWADVRZVWHVUBVRVWTUYRDEUVGSUWADUUQVAUURUUSEBVU
      BUUTYDYRYRVVPVJVWNVWMVLVUEEUVAVVPUVBWEUVCYSVVRUWTMUYRUWTYTSUVDUNYPUYSVUJV
      UFDOZAUGZUXBPUYSVUFUWIKZVUJVXBMUYSVXCBNVUFRZUYSVUMNVUDXKZVUFRZVXDUYSVUBNV
      UARZVUQVUSVXFUYSCNUWSRZVVAVXGUYRVXHUXDUYRVUTUYNVXHVVBWBCQNUWSUVEUVFUNVVEV
      UBCNUWSUYTVBVCVVGVVIVUBVUCNVUDVUAVUEXSXTUYSVUMVXEBNVUFVVKVXENMZUYSVUDNVRZ
      VXIPNKVXJXOPNYFWEVUDNYGYHSYIUQUWDVXCVXDVLZUYQUXDUWDNJKUVSVXKWDUYANBVUFJJU
      OUPUSVEIVUFUWLVXBUWIUWMUWJVUFMUWKVXAAUWJVUFDWHWIUYOVXAAWKWLVAUYSVXAUWSAUY
      SVXAVUADOZVUEDOZXKZUWSUBCLZOZTXKZUWSVXAVXNMUYSVUAVUEDUVHSUYSVXLVXPVXMTUYS
      VXLUWSUYTDOZOZVXPUWSUYTDUVIUYSUVTVXSVXPMVVDUVTVXRVXOUWSCBDUVJVIVAYRVXMTMZ
      UYSVXTVWOVUBXLZTMVYAVUCVUBXLVURTVWOVUCVUBVWRUVKVUCVUBUVLVVHUVMVUEDUVNUVOS
      YSUYSVXQVXPUWSVXPYTUYSVUTVXPUWSMVVCCQUWSUVPVAYRVPWIUYRUXAUXCWMVPUWPVUIVUK
      UIGVUFUWQUWFVUFMZUWHVUIUWOVUKVYBUWGVUHUWEUWFVUFEWOWRVYBUWNVUJPUWFVUFUWMXH
      WSWTXAXBXCXDUVQUVR $.
      $( [7-Oct-2014] $)
  $}

  ${
    $d A a d e $.  $d N a d e $.  $d a b c d e $.
    $( Lemma for ~ eldioph2 .  Construct necessary renaming function for one
       direction. $)
    eldioph2lem1 $p |- ( ( N e. NN0 /\ A e. Fin /\ ( 1 ... N ) C_ A ) -> E. d
        e. ( ZZ>= ` N ) E. e e. _V ( e : ( 1 ... d ) -1-1-onto-> A /\ ( e |` (
        1 ... N ) ) = ( _I |` ( 1 ... N ) ) ) ) $=
      ( wcel cfn c1 cfz co chash cfv wf1o wceq cvv wbr cun c0 a1i syl wb va cn0
      wss w3a caddc cdif cv wex cres cid wa wrex cuz cc cr nn0re 3ad2ant1 recnd
      cen ax-1cn addcom sylancl diffi 3ad2ant2 fzfid incom disjdif eqtri hashun
      cin syl3anc uncom simp3 undif sylib syl5eq fveq2d hashfz1 3eqtr3d oveq12d
      oveq2d cz 1z hashcl nn0z fzen ovex ensym fzfi hashen mp2an sylibr sylancr
      3eqtrd mpbid breng cle simpl1 simpl2 nn0addge2 syl2anc breqtrrd syl3anbrc
      adantr eluz2 vex resiexg ax-mp unex simpr f1oi ltp1 fzdisj f1oun syl22anc
      clt fzsplit1nn0 syl6reqr simpl3 f1oeq23 resundir dmres f1odm adantl eqtrd
      cdm ineq2d relres reldm0 residm uneq12d oveq2 f1oeq2 anbi1d f1oeq1 reseq1
      wrel un0 eqeq1d anbi12d rcla42ev syl112anc ex exlimdv mpd ) CUBEZAFEZGCHI
      ZAUCZUDZCGUEIZAJKZHIZAUUHUFZUAUGZLZUAUHZGDUGZHIZABUGZLZUUTUUHUIZUJUUHUIZM
      ZUKZBNULDCUMKZULZUUJUUMUUNUSOZUUQUUJUUMJKZUUNJKZMZUVHUUJUVIGCUEIZUVJCUEIZ
      HIZJKZGUVJHIZJKZUVJUUJUUMUVNJUUJUUKUVLUULUVMHUUJCUNEGUNEUUKUVLMUUJCUUFUUG
      CUOEZUUICUPZUQZURUTCGVAVBUUJUUNUUHPZJKZUVJUUHJKZUEIZUULUVMUUJUUNFEZUUHFEU
      UNUUHVJZQMZUWBUWDMUUGUUFUWEUUIAUUHVCVDZUUJGCVEUWGUUJUWFUUHUUNVJQUUNUUHVFU
      UHAVGVHZRUUNUUHVIVKUUJUWAAJUUJUWAUUHUUNPZAUUNUUHVLZUUJUUIUWJAMZUUFUUGUUIV
      MUUHAVNZVOVPVQUUJUWCCUVJUEUUFUUGUWCCMUUICVRUQWAVSZVTVQUUJUVNUVPUSOZUVOUVQ
      MZUUJUVPUVNUSOZUWOUUJGWBEZUVJWBEZCWBEZUWQUWRUUJWCRUUJUVJUBEZUWSUUJUWEUXAU
      WHUUNWDSZUVJWESUUFUUGUWTUUICWEZUQCGUVJWFVKUVPUVNUVLUVMHWGWHSUVNFEUVPFEUWP
      UWOTUVLUVMWIGUVJWIUVNUVPWJWKWLUUJUXAUVQUVJMUXBUVJVRSWNUUJUUMFEUWEUVKUVHTU
      UKUULWIUWHUUMUUNWJWMWOUUJUWEUVHUUQTUWHUUMUUNFUAWPSWOUUJUUPUVGUAUUJUUPUVGU
      UJUUPUKZUULUVFEZUUOUVCPZNEZGUULHIZAUXFLZUXFUUHUIZUVCMZUVGUXDUWTUULWBEZCUU
      LWQOZUXEUXDUUFUWTUUFUUGUUIUUPWRZUXCSUXDUULUBEZUXLUXDUUGUXOUUFUUGUUIUUPWSA
      WDSZUULWESUUJUXMUUPUUJCUVMUULWQUUJUVRUXACUVMWQOUVTUXBCUVJWTXAUWNXBXDZCUUL
      XEXCUXGUXDUUOUVCUAXFUUHNEUVCNEGCHWGUUHNXGXHXIRUXDUUMUUHPZUWAUXFLZUXIUXDUU
      PUUHUUHUVCLZUUMUUHVJZQMUWGUXSUUJUUPXJUXTUXDUUHXKRUXDUYAUUHUUMVJZQUUMUUHVF
      UXDUUFCUUKXPOZUYBQMUXNUXDUVRUYCUXDUUFUVRUXNUVSSCXLSUBGCUUKUULXMXAZVPUWGUX
      DUWIRUUMUUNUUHUUHUUOUVCXNXOUXDUXRUXHMUWAAMUXSUXITUXDUXHUUHUUMPZUXRUXDUUFU
      XOUXMUXHUYEMUXNUXPUXQCUULXQVKUUMUUHVLXRUXDUWAUWJAUWKUXDUUIUWLUUFUUGUUIUUP
      XSUWMVOVPUXRUXHUWAAUXFXTXAWOUXDUXJUUOUUHUIZUVCUUHUIZPZQUVCPZUVCUXJUYHMUXD
      UUOUVCUUHYARUXDUYFQUYGUVCUXDUYFYFZQMZUYFQMZUXDUYJUUHUUOYFZVJZQUUOUUHYBUXD
      UYNUYBQUXDUYMUUMUUHUUPUYMUUMMUUJUUMUUNUUOYCYDYGUYDYEVPUYFYQUYLUYKTUUOUUHY
      HUYFYIXHWLUYGUVCMUXDUJUUHYJRYKUYIUVCMUXDUYIUVCQPUVCQUVCVLUVCYRVHRWNUVEUXI
      UXKUKUXHAUUTLZUVDUKDBUULUXFUVFNUURUULMZUVAUYOUVDUYPUUSUXHMUVAUYOTUURUULGH
      YLUUSUXHAUUTYMSYNUUTUXFMZUYOUXIUVDUXKUXHAUUTUXFYOUYQUVBUXJUVCUUTUXFUUHYPY
      SYTUUAUUBUUCUUDUUE $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d N a b c $.  $d S a b c $.  $d A a b c $.
    $( Lemma for ~ eldioph2 .  Construct necessary renaming function for one
       direction. $)
    eldioph2lem2 $p |- ( ( ( N e. NN0 /\ -. S e. Fin ) /\ ( ( 1 ... N ) C_ S /\
        A e. ( ZZ>= ` N ) ) ) -> E. c ( c : ( 1 ... A ) -1-1-> S /\ ( c |` ( 1
        ... N ) ) = ( _I |` ( 1 ... N ) ) ) ) $=
      ( va wcel cfn wa c1 cfz wss wf1 cres wceq cun cin c0 adantl a1i syl wn co
      cn0 cuz cfv cdif cv wex cid simplr difinf sylancl diffi ax-mp isinffi crn
      fzfi wf1o f1f1orn incom disjdif eqtri wf f1f frn ssrin syl6sseq ss0 f1oun
      f1oi syl22anc f1of1 wb uncom simplrr fzss2 undif sylib syl5eq f1eq2 mpbid
      difss syl6ss simplrl unssd f1ss syl2anc resundir dmres f1dm ineq1d syl6eq
      cdm wrel relres reldm0 sylibr residm uneq12d un0 3eqtrd vex cvv ovex unex
      resiexg f1eq1 reseq1 eqeq1d anbi12d cla4ev ex exlimdv mpd ) CUCFZBGFUAZHZ
      ICJUBZBKZACUDUEFZHZHZIAJUBZXRUFZBXRUFZEUGZLZEUHZYCBDUGZLZYIXRMZUIXRMZNZHZ
      DUHZYBYEGFUAZYDGFZYHYBXPXRGFYPXOXPYAUJICUQBXRUKULYCGFYQIAUQYCXRUMUNYEYDEU
      OULYBYGYOEYBYGYOYBYGHZYCBYFYLOZLZYSXRMZYLNZYOYRYCYFUPZXROZYSLZUUDBKYTYRYD
      XROZUUDYSLZUUEYRUUFUUDYSURZUUGYRYDUUCYFURZXRXRYLURZYDXRPZQNZUUCXRPZQNZUUH
      YGUUIYBYDYEYFUSRUUJYRXRVJSUULYRUUKXRYDPQYDXRUTXRYCVAVBZSYRUUMQKUUNYRUUMYE
      XRPZQYRUUCYEKZUUMUUPKYGUUQYBYGYDYEYFVCUUQYDYEYFVDYDYEYFVETZRUUCYEXRVFTUUP
      XRYEPQYEXRUTXRBVAVBVGUUMVHTYDUUCXRXRYFYLVIVKUUFUUDYSVLTYRUUFYCNUUGUUEVMYR
      UUFXRYDOZYCYDXRVNYRXRYCKZUUSYCNYRXTUUTXQXSXTYGVOCIAVPTXRYCVQVRVSUUFYCUUDY
      SVTTWAYRUUCXRBYGUUCBKYBYGUUCYEBUURBXRWBWCRXQXSXTYGWDWEYCUUDBYSWFWGYRUUAYF
      XRMZYLXRMZOZQYLOZYLUUAUVCNYRYFYLXRWHSYRUVAQUVBYLYRUVAWMZQNZUVAQNZYRUVEXRY
      FWMZPZQYFXRWIYRUVIUVHXRPZQXRUVHUTYRUVJUUKQYRUVHYDXRYGUVHYDNYBYDYEYFWJRWKU
      UOWLVSVSUVAWNUVGUVFVMYFXRWOUVAWPUNWQUVBYLNYRUIXRWRSWSUVDYLNYRUVDYLQOYLQYL
      VNYLWTVBSXAYNYTUUBHDYSYFYLEXBXRXCFYLXCFICJXDXRXCXFUNXEYIYSNZYJYTYMUUBYCBY
      IYSXGUVKYKUUAYLYIYSXRXHXIXJXKWGXLXMXN $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d P a b c e t u g h $.  $d S a b c d e t u g h $.
    $d N a b c d e f t u g h $.
    $( Construct a Diophantine set from a polynomial with witness variables
       drawn from any set whatsoever, via ~ mzpcompact . $)
    eldioph2 $p |- ( ( N e. NN0 /\ ( S e. _V /\ ( 1 ... N ) C_ S ) /\ P e. (
        mzPoly ` S ) ) ->
        { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0
        ) } e. ( Dioph ` N ) ) $=
      ( va ve wcel cvv co wss wa cfv cv cres wceq wrex cfn cc0 ccom vb vc vd vg
      vh cn0 c1 cfz cmzp w3a cz cmap cmpt cab cdioph mzpcompact2 3ad2ant3 fveq1
      eqeq1d anbi2d rexbidv abbidv ad2antll wi cun wf1o cid cuz simplll simplrl
      fzfi unfi sylancl a1i eldioph2lem1 syl3anc ccnv wfun wrel elmapfun funrel
      ssun2 coires1 eqcomd adantl f1ococnv2 ad2antrl reseq1 ssun1 resabs1 ax-mp
      3syl syl syl6req resco syl6eq adantr coeq2d coass eqcomi 3eqtrd fveq2d wf
      ovex simprl ad2antrr ad3antrrr simpr wf1 f1of1 unssd f1ss syl2anc mapco2g
      simprr f1f syl22anc coeq1 eqid fvex fvmpt eqtr4d mpteq2dva fveq1d diophrw
      simpll simplrr f1ocnv f1of fssres mzprename eldioph eqeltrd ex rexlimdvva
      eqtrd mpd exp31 3adant3 imp31 adantrr ) EUFHZDIHZUGEUHJZDKZLZCDUIMHZUJZFN
      ZDKZCGUKDULJZGNZUUIOZUANZMZUMZPZLZUAUUIUIMZQFRQZBNZANZUUDOPZUVBCMZSPZLZAU
      FDULJZQZBUNZEUOMZHZUUGUUBUUTUUFCDFUAGUPUQUUHUURUVKFUARUUSUUHUUIRHZUUNUUSH
      ZLZLZUURUVKUVOUURLUVIUVCUVBUUPMZSPZLZAUVGQZBUNZUVJUUQUVIUVTPUVOUUJUUQUVHU
      VSBUUQUVFUVRAUVGUUQUVEUVQUVCUUQUVDUVPSUVBCUUPURUSUTVAVBVCUVOUUJUVTUVJHZUU
      QUUHUVNUUJUWAUUBUUFUVNUUJUWAVDVDUUGUUBUUFLZUVNUUJUWAUWBUVNLZUUJLZUGUBNZUH
      JZUUIUUDVEZUCNZVFZUWHUUDOVGUUDOPZLZUCIQUBEVHMZQZUWAUWDUUBUWGRHZUUDUWGKZUW
      MUUBUUFUVNUUJVIUWDUVLUUDRHUWNUWBUVLUVMUUJVJUGEVKUUIUUDVLVMUWOUWDUUDUUIWBV
      NUWGUCEUBVOVPUWDUWKUWAUBUCUWLIUWDUWEUWLHZUWHIHZLZLZUWKUWAUWSUWKLZUVTUVAUD
      NZUUDOPUXAUEUKUWFULJZUENZUWHVQZUUIOZTZUUNMZUMZMSPLUDUFUWFULJQBUNZUVJUWTUV
      TUVCUVBGUUKUULUWHTZUXHMZUMZMZSPZLZAUVGQZBUNZUXIUWTUVSUXPBUWTUVRUXOAUVGUWT
      UVQUXNUVCUWTUVPUXMSUWTUVBUUPUXLUWTGUUKUUOUXKUWTUULUUKHZLZUUOUXJUXETZUUNMZ
      UXKUXSUUMUXTUUNUXSUUMUULVGUUIOZTZUULUWHUXETZTZUXTUXRUUMUYCPZUWTUXRUULVRUU
      LVSZUYFUULUKDVTUULWAUYGUYCUUMUULUUIWCWDWLWEUXSUYBUYDUULUWTUYBUYDPUXRUWTUY
      BUWHUXDTZUUIOZUYDUWTUYIVGUWGOZUUIOZUYBUWTUYHUYJPZUYIUYKPUWIUYLUWSUWJUWFUW
      GUWHWFWGUYHUYJUUIWHWMUUIUWGKZUYKUYBPUUIUUDWIZVGUUIUWGWJWKWNUWHUXDUUIWOWPW
      QWRUYEUXTPUXSUXTUYEUULUWHUXEWSWTVNXAXBUXSUXJUXBHZUXKUYAPUXSUWFIHZUUCUXRUW
      FDUWHXCZUYOUYPUXSUGUWEUHXDZVNUWDUUCUWRUWKUXRUWBUUCUVNUUJUUBUUCUUEXEXFXGUW
      TUXRXHUWTUYQUXRUWTUWFDUWHXIZUYQUWTUWFUWGUWHXIZUWGDKZUYSUWIUYTUWSUWJUWFUWG
      UWHXJWGUWDVUAUWRUWKUWDUUIUUDDUWCUUJXHUWBUUEUVNUUJUUBUUCUUEXOXFXKXFUWFUWGD
      UWHXLXMZUWFDUWHXPWMWQUULUKDUWHUWFXNXQUEUXJUXGUYAUXBUXHUXCUXJPUXFUXTUUNUXC
      UXJUXEXRXBUXHXSUXTUUNXTYAWMYBYCYDUSUTVAVBUWTUUCUYSUWJUXQUXIPUWCUUCUUJUWRU
      WKUUBUUCUUEUVNVJXGVUBUWSUWIUWJXOUXHDUWFUWHUUDBAUDGYEVPYPUWTUUBUWPUXHUWFUI
      MHZUXIUVJHUWCUUBUUJUWRUWKUUBUUFUVNYFXGUWDUWPUWQUWKVJUWTUYPUVMUUIUWFUXEXCZ
      VUCUYPUWTUYRVNUWDUVMUWRUWKUWBUVLUVMUUJYGXFUWIVUDUWSUWJUWIUWGUWFUXDXCZUYMV
      UDUWIUWGUWFUXDVFVUEUWFUWGUWHYHUWGUWFUXDYIWMUYNUWGUWFUUIUXDYJVMWGUEUXEUUNU
      UIUWFYKVPUDBUXHUWEEYLVPYMYNYOYQYRYSYTUUAYMYNYOYQ $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A a b p $.  $d N a b c d e u t p $.  $d S a b c d e u t p $.

    $( While Diophantine sets were defined to have a finite number of witness
       variables consequtively following the observable variables, this is not
       necessary; they can equivalently be taken to use any witness set
       ` ( S \ ( 1 ... N ) ) ` .  For instance, in ~ diophin we use this to
       take the two input sets to have disjoint witness sets. $)
    eldioph2b $p |- ( ( ( N e. NN0 /\ S e. _V ) /\ ( -. S e. Fin /\ ( 1 ... N )
        C_ S ) ) -> ( A e. ( Dioph ` N ) <->
        E. p e. ( mzPoly ` S ) A = { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1
        ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( vd vb va vc ve wcel cvv wa co cfv cv cres wceq wrex cn0 cfn cfz wss cc0
      wn c1 cdioph cmap cab cuz eldiophb wf1 cid simplll simplrl simplrr simprl
      cmzp eldioph2lem2 syl22anc rexv sylibr cz ccom wf simplr ad3antrrr simprr
      wex ad2antrr f1f syl mzprename syl3anc diophrw eqcomd fveq1 eqeq1d anbi2d
      cmpt w3a rexbidv abbidv eqeq2d rcla4ev syl2anc rexlimdva eqeq1 syl5ibrcom
      ex mpd rexlimdvva adantld syl5bi simpr simpllr eldioph2 syl121anc eqeltrd
      adantr impbid ) EUALZDMLZNZDUBLUFZUGEUCOZDUDZNZNZCEUHPZLZCBQZAQZXGRSZXNFQ
      ZPZUESZNZAUADUIOZTZBUJZSZFDUSPZTZXLXCCXMGQZXGRSYFHQZPUESNGUAUGIQZUCOZUIOT
      BUJZSZHYIUSPZTIEUKPZTZNXJYEGBCIEHULXJYNYEXCXJYKYEIHYMYLXJYHYMLZYGYLLZNZNZ
      YEYKYJYBSZFYDTZYRYIDJQZUMZUUAXGRUNXGRSZNZJMTZYTYRUUDJVJZUUEYRXCXFXHYOUUFX
      CXDXIYQUOXEXFXHYQUPXEXFXHYQUQXJYOYPURYHDEJUTVAUUDJVBVCYRUUDYTJMYRUUAMLZNZ
      UUDYTUUHUUDNZKVDDUIOKQUUAVEYGPWAZYDLZYJXOXNUUJPZUESZNZAXTTZBUJZSZYTUUIXDY
      PYIDUUAVFZUUKXJXDYQUUGUUDXCXDXIVGVHZYRYPUUGUUDXJYOYPVIVKUUIUUBUURUUHUUBUU
      CURZYIDUUAVLVMKUUAYGYIDVNVOUUIXDUUBUUCUUQUUSUUTUUHUUBUUCVIXDUUBUUCWBUUPYJ
      YGDYIUUAXGBAGKVPVQVOYSUUQFUUJYDXPUUJSZYBUUPYJUVAYAUUOBUVAXSUUNAXTUVAXRUUM
      XOUVAXQUULUEXNXPUUJVRVSVTWCWDWEWFWGWKWHWLYKYCYSFYDCYJYBWIWCWJWMWNWOXJYCXL
      FYDXJXPYDLZNZYCXLUVCYCNCYBXKUVCYCWPUVCYBXKLZYCUVCXCXDXHUVBUVDXCXDXIUVBUOX
      CXDXIUVBWQXEXFXHUVBUQXJUVBWPABXPDEWRWSXAWTWKWHXB $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A a b c d $.  $d B a b c d $.
    $( Remove antecedent on ` B ` from Diophantine set contructors. $)
    eldiophelnn0 $p |- ( A e. ( Dioph ` B ) -> B e. NN0 ) $=
      ( vc vd va vb cdioph cfv wcel cn0 cv c1 cfz co cres wceq cc0 wa cmap wrex
      cab cmzp cuz eldiophb simplbi ) ABGHIBJIACKDKZLBMNOPUFEKHQPRDJLFKMNZSNTCU
      APEUGUBHTFBUCHTDCAFBEUDUE $.
      $( [10-Oct-2014] $)
  $}

  ${
    $d A p t u $.  $d N p t u $.
    $( Define Diophantine sets in terms of polynomials with variables indexed
       by ` NN ` .  This avoids a quantifier over the number of witness
       variables and will be easier to use than ~ eldiophb in most cases. $)
    eldioph3b $p |- ( A e. ( Dioph ` N ) <-> ( N e. NN0 /\
        E. p e. ( mzPoly ` NN ) A = { t | E. u e. ( NN0 ^m NN ) ( t = ( u |` (
        1 ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( cdioph cfv wcel cn0 wa cv co wceq cn wrex cvv wb cfn com mpan2 cfz cres
      c1 cc0 cmap cab cmzp eldiophelnn0 pm4.71ri nnex wn wss ominf cen wbr omex
      nnenom enfi mp2an mtbir elfznn ssriv pm3.2i eldioph2b pm5.32i bitri ) CDF
      GHZDIHZVGJVHCBKAKZUCDUALZUBMVIEKZGUDMJAINUELOBUFMENUGGOZJVGVHCDUHUIVHVGVL
      VHNPHZVGVLQZUJVHVMJNRHZUKZVJNULZJVNVPVQVOSRHZUMSPHNSUNUOVOVRQUPUQNSPURUSU
      TEVJNVKDVAVBVCABCNDEVDTTVEVF $.
      $( [10-Oct-2014] $)
  $}

  $( could maybe shorten a LOT of these with a canned substitution huh? $)
  ${
    $d A a b p t u $.  $d N a b p t u $.  $d P a b p t u $.
    $( Inference version of ~ eldioph3b with quantifier expanded. $)
    eldioph3 $p |- ( ( N e. NN0 /\ P e. ( mzPoly ` NN ) ) -> { t | E. u e. (
        NN0 ^m NN ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0 ) } e. ( Dioph
        ` N ) ) $=
      ( va vb vp cn0 wcel cn cfv wa cv co cres wceq cc0 wrex cab eqeq1d cmzp c1
      cfz cdioph simpl simpr eqidd fveq1 anbi2d rexbidv abbidv weq eqeq1 anbi1d
      cmap reseq1 eqeq2d anbi12d cbvrexv syl6bb cbvabv syl6eq rcla4ev eldioph3b
      fveq2 syl2anc sylanbrc ) DHIZCJUAKZIZLZVHBMZAMZUBDUCNZOZPZVMCKZQPZLZAHJUO
      NZRZBSZEMZFMZVNOZPZWDGMZKZQPZLZFVTRZESZPZGVIRZWBDUDKIVHVJUEVKVJWBWBPZWNVH
      VJUFVKWBUGWMWOGCVIWGCPZWLWBWBWPWLWFWDCKZQPZLZFVTRZESWBWPWKWTEWPWJWSFVTWPW
      IWRWFWPWHWQQWDWGCUHTUIUJUKWTWAEBEBULZWTVLWEPZWRLZFVTRWAXAWSXCFVTXAWFXBWRW
      CVLWEUMUNUJXCVSFAVTFAULZXBVPWRVRXDWEVOVLWDVMVNUPUQXDWQVQQWDVMCVETURUSUTVA
      VBUQVCVFFEWBDGVDVG $.
      $( [10-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 2 miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If two functions agree on their common domain, express their union as a
     union of three functions with pairwise disjoint domains. $)
  resasplit $p |- ( ( F Fn A /\ G Fn B /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i
      B ) ) ) -> ( F u. G ) = ( ( F |` ( A i^i B ) ) u. ( ( F |` ( A \ B ) ) u.
      ( G |` ( B \ A ) ) ) ) ) $=
    ( wfn cin cres w3a cun fnresdm uneq12 syl2an inundif reseq2i resundi eqtr3i
    wceq cdif uneq1i syl6eq 3adant3 simp3 uneq1d uneq2d incom eqtri uneq12i un4
    syl6reqr unidm eqtr3d ) CAEZDBEZCABFZGZDUNGZQZHZCAGZDBGZIZCDIZUOCABRZGZDBAR
    ZGZIZIZULUMVAVBQZUQULUSCQUTDQVIUMACJBDJUSCUTDKLUAURVAUOUOIZVGIZVHURVAUOVDIZ
    UOVFIZIZVKURVNVLUPVFIZIVAURVMVOVLURUOUPVFULUMUQUBUCUDUSVLUTVOCUNVCIZGUSVLVP
    ACABMNCUNVCOPDUNVEIZGUTVOVQBDVQBAFZVEIBUNVRVEABUESBAMUFNDUNVEOPUGUIUOVDUOVF
    UHTVJUOVGUOUJSTUK $.
    $( [9-Oct-2014] $)

  $( The union of two functions which agree on their common domain is a
     function. $)
  fresaun $p |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = ( G |`
      ( A i^i B ) ) ) -> ( F u. G ) : ( A u. B ) --> C ) $=
    ( wf cin cres wceq cun c0 wss fssres sylancl difss disjdif 3eqtri a1i eqtri
    cdif w3a simp1 inss1 simp2 indifdir difeq1i 0dif syl21anc indi inass ineq2i
    fun in0 incom ineq1i uneq12i un0 wfn ffn resasplit syl3an feq1d un12 uneq1i
    id inundif uneq2i undif1 unidm feq23i syl6rbbr mpbid ) ACDFZBCEFZDABGZHZEVO
    HIZUAZVOABTZBATZJZJZCCCJZJZVPDVSHZEVTHZJZJZFZABJZCDEJZFZVRVOCVPFZWAWCWGFZVO
    WAGZKIZWIVRVMVOALWMVMVNVQUBZABUCACVODMNVRVSCWEFZVTCWFFZVSVTGZKIZWNVRVMVSALW
    RWQABOACVSDMNVRVNVTBLWSVMVNVQUDBAOBCVTEMNXAVRWTAVTGZBVTGZTKXCTKABVTUEXBKXCA
    BPZUFXCUGQRVSVTCCWEWFULUHWPVRWOVOVSGZVOVTGZJKKJKVOVSVTUIXEKXFKXEABVSGZGAKGK
    ABVSUJXGKABAPUKAUMQXFBAGZVTGZKVOXHVTABUNZUOXIBXBGBKGKBAVTUJXBKBXDUKBUMQSUPK
    UQQRVOWACWCVPWGULUHVRWLWJCWHFWIVRWJCWKWHVMDAURVNEBURVQVQWKWHIACDUSBCEUSVQVE
    ABDEUTVAVBWBWDWJCWHWBVSVOVTJZJVSBJWJVOVSVTVCXKBVSXKXHVTJBVOXHVTXJVDBAVFSVGA
    BVHQWDWCCWCCCCVIZVGXLSVJVKVL $.
    $( [9-Oct-2014] $)

  $( From the union of two functions that agree on the domain overlap, either
     component can be recovered by restriction. $)
  fresaunres2 $p |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = (
      G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G ) $=
    ( wf cin cres wceq cun cdif wfn ffn syl resundir ax-mp c0 cdm eqtri syl5eq
    w3a resasplit syl3an reseq1 wss inss2 resabs2 uneq12i ineq2i disjdif ineq1i
    id dmres inass inss1 eqssi 3eqtr3i wrel wb relres reldm0 mpbir difss uneq2i
    0ss simp3 uneq1d wa uncom un0 resundi uneq1i inundif reseq2i fnresdm adantl
    incom syl5eqr 3adant3 eqtrd ) ACDFZBCEFZDABGZHZEWCHZIZUAZDEJZBHZWDDABKZHZEB
    AKZHZJZJZBHZEWGWHWOIZWIWPIWADALWBEBLZWFWFWQACDMBCEMZWFULABDEUBUCWHWOBUDNWGW
    PWDBHZWNBHZJZEWDWNBOWGXBWDWKBHZWMBHZJZJZEWTWDXAXEWCBUEWTWDIABUFDWCBUGPWKWMB
    OUHWGXFWDQWMJZJZEXEXGWDXCQXDWMXCQIZXCRZQIZXJBWKRZGZQWKBUMXMBWJDRZGZGZQXLXOB
    DWJUMUIBWJGZXNGQXNGZXPQXQQXNBAUJUKBWJXNUNXRQQXNUOXRVEUPUQSSXCURXIXKUSWKBUTX
    CVAPVBWLBUEXDWMIBAVCEWLBUGPUHVDWGXHWEXGJZEWGWDWEXGWAWBWFVFVGWAWBXSEIWFWAWBV
    HZXSWEWMJZEXGWMWEXGWMQJWMQWMVIWMVJSVDXTYAEWCWLJZHZEEWCWLVKXTYCEBHZEYBBEYBBA
    GZWLJBWCYEWLABVQVLBAVMSVNWBYDEIZWAWBWRYFWSBEVONVPTVRTVSVTTTTVT $.
    $( [9-Oct-2014] $)

  ${
    $d N a $.  $d A a $.  $d B a $.

    $( Membership in a set of lower integers. $)
    ellz1 $p |- ( B e. ZZ -> ( A e. ( ZZ \ ( ZZ>= ` ( B + 1 ) ) ) <-> ( A e. ZZ
        /\ A <_ B ) ) ) $=
      ( cz c1 caddc co cuz cfv cdif wcel wn wa cle wbr eldif clt notbid cr zre
      wb zltp1le lenlt syl2anr peano2z eluz sylan 3bitr4rd pm5.32da syl5bb ) AC
      BDEFZGHZIJACJZAUKJZKZLBCJZULABMNZLACUKOUOULUNUPUOULLZBAPNZKZUJAMNZKUPUNUQ
      URUTBAUAQULARJBRJUPUSTUOASBSABUBUCUQUMUTUOUJCJULUMUTTBUDUJAUEUFQUGUHUI $.
      $( [9-Oct-2014] $)

    $( A set of lower integers and upper integers which abut or overlap is all
       of the integers. $)
    lzunuz $p |- ( ( A e. ZZ /\ B e. ZZ /\ B <_ ( A + 1 ) ) -> ( ( ZZ \ ( ZZ>=
        ` ( A + 1 ) ) ) u. ( ZZ>= ` B ) ) = ZZ ) $=
      ( va cz wcel c1 caddc co cle wbr w3a cuz cfv wo wa wb cr zre syl ex ellz1
      cdif cun cv 3ad2ant1 eluz1 3ad2ant2 orbi12d wi clt adantl simpl1 lelttric
      elun syl2anc simpll2 simpll1 peano2z 3syl ad2antlr simpll3 zltp1le biimpa
      3ad2antl1 letrd orim2d mpd pm4.71 sylib andi syl6rbb bitrd syl5bb eqrdv )
      ADEZBDEZBAFGHZIJZKZCDVQLMUBZBLMZUCZDCUDZWBEWCVTEZWCWAEZNZVSWCDEZWCVTWAUNV
      SWFWGWCAIJZOZWGBWCIJZOZNZWGVSWDWIWEWKVOVPWDWIPVRWCAUAUEVPVOWEWKPVRBWCUFUG
      UHVSWGWGWHWJNZOZWLVSWGWMUIWGWNPVSWGWMVSWGOZWHAWCUJJZNZWMWOWCQEZAQEZWQWGWR
      VSWCRZUKWOVOWSVOVPVRWGULARSWCAUMUOWOWPWJWHWOWPWJWOWPOZBVQWCXAVPBQEVOVPVRW
      GWPUPBRSXAVOVQDEVQQEVOVPVRWGWPUQAURVQRUSWGWRVSWPWTUTVOVPVRWGWPVAWOWPVQWCI
      JZVOVPWGWPXBPVRAWCVBVDVCVETVFVGTWGWMVHVIWGWHWJVJVKVLVMVN $.
      $( [9-Oct-2014] $)

    $( Express a one-based finite range as the intersection of lower integers
       with ` NN ` . $)
    fz1eqin $p |- ( N e. NN0 -> ( 1 ... N ) = ( ( ZZ \ ( ZZ>= ` ( N + 1 ) ) )
        i^i NN ) ) $=
      ( va cn0 wcel c1 cfz co cz caddc cuz cfv cdif cn cin cv cle wbr wa w3a wb
      1z nn0z elfz1 sylancr 3anass ancom anbi2i anandi 3bitri syl6bb elin ellz1
      syl elnnz1 a1i anbi12d syl5bb bitr4d eqrdv ) ACDZBEAFGZHAEIGJKLZMNZUTBOZV
      ADZVDHDZVDAPQZRZVFEVDPQZRZRZVDVCDZUTVEVFVIVGSZVKUTEHDAHDZVEVMTUAAUBZVDEAU
      CUDVMVFVIVGRZRVFVGVIRZRVKVFVIVGUEVPVQVFVIVGUFUGVFVGVIUHUIUJVLVDVBDZVDMDZR
      UTVKVDVBMUKUTVRVHVSVJUTVNVRVHTVOVDAULUMVSVJTUTVDUNUOUPUQURUS $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d N a b c $.
    $( Lower integers are countably infinite. $)
    lzenom $p |- ( N e. ZZ -> ( ZZ \ ( ZZ>= ` ( N + 1 ) ) ) ~~ om ) $=
      ( cz wcel c1 co cn cen wbr cmin cvv cle wa wceq syl2anc cc cr wb ad2antrl
      sseldi anbi12d va vb caddc cuz cfv cdif com cv zex difexg ax-mp a1i a1i12
      ovex simpl peano2zdi simprl zsubcl simprr zcn adantr ax-1cn pncan sylancl
      breqtrrd zre zssre 1re lesub syl3anc mpbid zsscn nncan eqcomd jca31 eleq1
      adantrr breq2 oveq2 eqeq2d ad2antll mpbird recnd pncan2 suble breq1 ellz1
      eqbrtrd impbida anbi1d elnnz1 3bitr4d en2d nnenom entr ) ABCZBADUCEZUDUEZ
      UFZFGHFUGGHWSUGGHWPUAUBWSFWQUAUHZIEZWQUBUHZIEZWSJCZWPBJCXDUIBWRJUJUKULWPW
      TWSCZXAJCWQWTIUNUMWPXBFCZXCJCWQXBIUNUMWPWTBCZWTAKHZLZXBXAMZLZXBBCZDXBKHZL
      ZWTXCMZLZXEXJLXFXOLWPXKXPWPXKLXPXABCZDXAKHZLZWTWQXAIEZMZLZWPXIYBXJWPXILZX
      QXRYAYCWQBCZXGXQYCAWPXIUOUPZWPXGXHUQWQWTURNYCWTWQDIEZKHZXRYCWTAYFKWPXGXHU
      SYCAOCZDOCZYFAMWPYHXIAUTVAVBADVCVDVEYCWTPCZWQPCZDPCZYGXRQXGYJWPXHWTVFRYCB
      PWQVGYESYLYCVHULWTWQDVIVJVKYCXTWTYCWQOCZWTOCZXTWTMYCBOWQVLYESXGYNWPXHWTUT
      RWQWTVMNVNVOVQXJXPYBQWPXIXJXNXSXOYAXJXLXQXMXRXBXABVPXBXADKVRTXJXCXTWTXBXA
      WQIVSVTTWAWBWPXPLXKXCBCZXCAKHZLZXBWQXCIEZMZLZWPXNYTXOWPXNLZYOYPYSUUAYDXLY
      OUUAAWPXNUOUPZWPXLXMUQWQXBURNUUAWQAIEZXBKHZYPUUAUUCDXBKUUAYHYIUUCDMUUAAWP
      APCZXNAVFVAZWCVBADWDVDWPXLXMUSWHUUAYKUUEXBPCZUUDYPQUUABPWQVGUUBSUUFXLUUGW
      PXMXBVFRWQAXBWEVJVKUUAYRXBUUAYMXBOCZYRXBMUUABOWQVLUUBSXLUUHWPXMXBUTRWQXBV
      MNVNVOVQXOXKYTQWPXNXOXIYQXJYSXOXGYOXHYPWTXCBVPWTXCAKWFTXOXAYRXBWTXCWQIVSV
      TTWAWBWIWPXEXIXJWTAWGWJWPXFXNXOXFXNQWPXBWKULWJWLWMWNWSFUGWOVD $.
      $( [10-Oct-2014] $)
  $}

  ${
    elmapresaun.1 $e |- A e. _V $.
    elmapresaun.2 $e |- B e. _V $.
    $( ~ fresaun transposed to mappings. $)
    elmapresaun $p |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\ ( F |` ( A i^i
        B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) e. ( C ^m ( A u. B ) ) )
        $=
      ( cmap co wcel cin cres cun wf cvv wb elmapex1 elmapg sylancl ibi wceq id
      w3a fresaun syl3an unex 3ad2ant1 mpbird ) DCAHIJZECBHIJZDABKZLEUKLUAZUCDE
      MZCABMZHIJZUNCUMNZUIACDNZUJBCENZULULUPUIUQUICOJZAOJUIUQPDCAQZFCADOORSTUJU
      RUJUSBOJUJURPECBQGCBEOORSTULUBABCDEUDUEUIUJUOUPPZULUIUSUNOJVAUTABFGUFCUNU
      MOORSUGUH $.
      $( [9-Oct-2014] $)

    $( ~ fresaunres2 transposed to mappings. $)
    elmapresaunres2 $p |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\ ( F |` ( A
        i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G ) $=
      ( cmap co wcel wf cin cres wceq cvv wb elmapex1 elmapg sylancl ibi cun id
      fresaunres2 syl3an ) DCAHIJZACDKZECBHIJZBCEKZDABLZMEUIMNZUJDEUABMENUEUFUE
      COJZAOJUEUFPDCAQFCADOORSTUGUHUGUKBOJUGUHPECBQGCBEOORSTUJUBABCDEUCUD $.
      $( [9-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 2: union and intersection.  Monotone Boolean algebra
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b c d e f g h i j k l $.  $d B a b c d e f g h i j k l $.
    $d N a b c d e f g h i j k l $.

    $( If two sets are Diophantine, so is their intersection. $)
    diophin $p |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A i^i B )
        e. ( Dioph ` N ) ) $=
      ( vc vg cfv wcel cn0 wa co cres wceq cc0 cz wrex cn a1i syl c2 syl3anc vd
      va ve vb vf cdioph cin wi eldiophelnn0 cv c1 cfz caddc cuz cdif cmap cmzp
      cab cvv cfn wn wss wb id1 zex difexg ax-mp com ominf cen omex nn0z lzenom
      enfi sylancr mtbiri fz1eqin inss1 eqsstrd eldioph2b syl22anc nnenom mp2an
      wbr nnex mtbir elfznn ssriv anbi12d reeanv cexp cmpt inab simplrl simplrr
      cun simprll simprrl eqtr3d eqcomd reseq2d 3eqtr4d elmapresaun nnuz uneq2i
      ad3antrrr syl5eq reseq1 elmapresaunres2 fveq2d eqtrd simprrr jca32 eqeq2d
      eqeq1d syl2anc ex rexlimdvva elmapssres adantr nnssz simprl resabs1 fveq2
      eqtr4d anbi2d cr zssre wf mzpf mp3an23 adantl ffvelrn sseldi mzpresrename
      cle oveq1d 2nn0 mzpexpmpt sylancl 1z nn0p1nn nnge1 lzunuz eleqtrd uneq12d
      oveq2d unidm syl5eqr resundir syl6eqr uncom incom simprlr simpr difss jca
      rcla4ev anbi1d rcla42ev rexlimdva impbid mapss sseli sumsqeq0 weq oveq12d
      nn0ssz eqid fvmpt bitr4d rexbidva bitrd syl5bbr abbidv simpl fzssuz uzssz
      ovex sstri pm3.2i simprr mzpaddmpt eldioph2 eqeltrd ineq12 eleq1d syl5bir
      syl5ibrcom sylbid anabsi5 ) ACUFFZGZBUWLGZABUGZUWLGZUWMCHGZUWMUWNIZUWPUHA
      CUIUWQUWRADUJZUAUJZUKCULJZKZLZUWTUBUJZFZMLZIZUAHNCUKUMJZUNFZUOZUPJZOZDURZ
      LZUBUXJUQFZOZBUWSUCUJZUXAKZLZUXQUDUJZFZMLZIZUCHPUPJZOZDURZLZUDPUQFZOZIZUW
      PUWQUWMUXPUWNUYIUWQUWQUXJUSGZUXJUTGZVAUXAUXJVBZUWMUXPVCUWQVDZUYKUWQNUSGZU
      YKVENUXIUSVFVGZQUWQUYLVHUTGZVIUWQVHUSGZUXJVHVJWDZUYLUYQVCVKUWQCNGZUYSCVLZ
      CVMRUXJVHUSVNVOVPUWQUXAUXJPUGZUXJCVQZVUBUXJVBUWQUXJPVRQVSZUADAUXJCUBVTWAU
      WQUWQPUSGZPUTGZVAZUXAPVBZUWNUYIVCUYNVUEUWQWEQVUGUWQVUFUYQVIUYRPVHVJWDVUFU
      YQVCVKWBPVHUSVNWCWFQVUHUWQUBUXAPUXDCWGWHZQUCDBPCUDVTWAWIUYJUXNUYGIZUDUYHO
      UBUXOOUWQUWPUXNUYGUBUDUXOUYHWJUWQVUJUWPUBUDUXOUYHUWQUXDUXOGZUXTUYHGZIZIZU
      WPVUJUXMUYFUGZUWLGVUNVUOUWSUEUJZUXAKZLZVUPENNUPJZEUJZUXJKZUXDFZSWKJZVUTPK
      ZUXTFZSWKJZUMJZWLZFZMLZIZUEHNUPJZOZDURZUWLVUNVUOUXLUYEIZDURVVNUXLUYEDWMVU
      NVVOVVMDVVOUXGUYCIZUCUYDOUAUXKOZVUNVVMUXGUYCUAUCUXKUYDWJVUNVVQVURVUPUXJKZ
      UXDFZMLZVUPPKZUXTFZMLZIZIZUEVVLOZVVMVUNVVQVWFVUNVVPVWFUAUCUXKUYDVUNUWTUXK
      GZUXQUYDGZIZIZVVPVWFVWJVVPIZUWTUXQWPZVVLGUWSVWLUXAKZLZVWLUXJKZUXDFZMLZVWL
      PKZUXTFZMLZIZIZVWFVWKVWLHUXJPWPZUPJZVVLVWKVWGVWHUWTVUBKZUXQVUBKZLZVWLVXDG
      VUNVWGVWHVVPWNZVUNVWGVWHVVPWOZVWKUXBUXRVXEVXFVWKUWSUXBUXRVWJUXCUXFUYCWQZV
      WJUXGUXSUYBWRZWSUWQVXEUXBLVUMVWIVVPUWQVUBUXAUWTUWQUXAVUBVUCWTZXAXFUWQVXFU
      XRLVUMVWIVVPUWQVUBUXAUXQVXLXAXFXBZUXJPHUWTUXQUYPWEXCTUWQVXDVVLLVUMVWIVVPU
      WQVXCNHUPUWQVXCUXJUKUNFZWPZNPVXNUXJXDXEUWQUYTUKNGZUKUXHYPWDZVXONLVUAVXPUW
      QUUAQUWQUXHPGVXQCUUBUXHUUCRCUKUUDTXGUUGXFUUEVWKVWNVWQVWTVWKUWSUXBUXRWPZVW
      MVWKUWSUWSUWSWPVXRUWSUUHVWKUWSUXBUWSUXRVXJVXKUUFUUIUWTUXQUXAUUJUUKVWKVWPU
      XEMVWKVWOUWTUXDVWKVWOUXQUWTWPZUXJKZUWTVWLVXSLVWOVXTLUWTUXQUULVWLVXSUXJXHV
      GVWKVWHVWGUXQPUXJUGZKZUWTVYAKZLVXTUWTLVXIVXHVWKUXRUXBVYBVYCVWKUWSUXRUXBVX
      KVXJWSUWQVYBUXRLVUMVWIVVPUWQVYAUXAUXQUWQVYAVUBUXAPUXJUUMVXLXGZXAXFUWQVYCU
      XBLVUMVWIVVPUWQVYAUXAUWTVYDXAXFXBPUXJHUXQUWTWEUYPXITXGXJVWJUXCUXFUYCUUNXK
      VWKVWSUYAMVWKVWRUXQUXTVWKVWGVWHVXGVWRUXQLVXHVXIVXMUXJPHUWTUXQUYPWEXITXJVW
      JUXGUXSUYBXLXKXMVWEVXBUEVWLVVLVUPVWLLZVURVWNVWDVXAVYEVUQVWMUWSVUPVWLUXAXH
      XNVYEVVTVWQVWCVWTVYEVVSVWPMVYEVVRVWOUXDVUPVWLUXJXHXJXOVYEVWBVWSMVYEVWAVWR
      UXTVUPVWLPXHXJXOWIWIUURXPXQXRVUNVWEVVQUEVVLVUNVUPVVLGZIZVWEVVQVYGVWEIZVVR
      UXKGZVWAUYDGZUWSVVRUXAKZLZVVTIZUWSVWAUXAKZLZVWCIZIZVVQVYGVYIVWEVYGVYFUXJN
      VBZUYOVYIVUNVYFUUOZVYRVYGNUXIUUPZQUYOVYGVEQZVUPHNUXJXSTXTVYGVYJVWEVYGVYFP
      NVBZUYOVYJVYSWUBVYGYAQWUAVUPHNPXSTXTVYHVYMVYOVWCVYHVYLVVTVYHUWSVUQVYKVYGV
      URVWDYBZVYHUYMVYKVUQLUWQUYMVUMVYFVWEVUDXFVUPUXAUXJYCRYEVYGVURVVTVWCWRUUQV
      YHUWSVUQVYNWUCVYHVUHVYNVUQLVUHVYHVUIQVUPUXAPYCRYEVYGVURVVTVWCXLXMVVPVYQVY
      MUYCIUAUCVVRVWAUXKUYDUWTVVRLZUXGVYMUYCWUDUXCVYLUXFVVTWUDUXBVYKUWSUWTVVRUX
      AXHXNWUDUXEVVSMUWTVVRUXDYDXOWIUUSUXQVWALZUYCVYPVYMWUEUXSVYOUYBVWCWUEUXRVY
      NUWSUXQVWAUXAXHXNWUEUYAVWBMUXQVWAUXTYDXOWIYFUUTTXQUVAUVBVUNVWEVVKUEVVLVYG
      VWDVVJVURVYGVWDVVSSWKJZVWBSWKJZUMJZMLZVVJVYGVVSYGGVWBYGGVWDWUIVCVYGNYGVVS
      YHVYGNUXJUPJZNUXDYIZVVRWUJGZVVSNGVYGVUKWUKUWQVUKVULVYFWNUXDUXJYJRVYFWULVU
      NVYFVUPVUSGZWULVVLVUSVUPHNVBVVLVUSVBUVHHNNVEVEUVCVGUVDZWUMVYRUYOWULVYTVEV
      UPNNUXJXSYKRYLWUJNVVRUXDYMXPYNVYGNYGVWBYHVYGNPUPJZNUXTYIZVWAWUOGZVWBNGVYG
      VULWUPUWQVUKVULVYFWOUXTPYJRVYFWUQVUNVYFWUMWUQWUNWUMWUBUYOWUQYAVEVUPNNPXSY
      KRYLWUONVWAUXTYMXPYNVVSVWBUVEXPVYGVVIWUHMVYGWUMVVIWUHLVYFWUMVUNWUNYLEVUPV
      VGWUHVUSVVHEUEUVFZVVCWUFVVFWUGUMWURVVBVVSSWKWURVVAVVRUXDVUTVUPUXJXHXJYQWU
      RVVEVWBSWKWURVVDVWAUXTVUTVUPPXHXJYQUVGVVHUVIWUFWUGUMUVSUVJRXOUVKYFUVLUVMU
      VNUVOXGVUNUWQUYOUXANVBZIZVVHNUQFZGZVVNUWLGUWQVUMUVPWUTVUNUYOWUSVEUXAVXNNU
      KCUVQUKUVRUVTUWAQVUNEVUSVVCWLWVAGZEVUSVVFWLWVAGZWVBVUNEVUSVVBWLWVAGZSHGZW
      VCVUNUYOVYRVUKWVEUYOVUNVEQZVYRVUNVYTQUWQVUKVULYBEUXDUXJNYOTYREVVBSNYSYTVU
      NEVUSVVEWLWVAGZWVFWVDVUNUYOWUBVULWVHWVGWUBVUNYAQUWQVUKVULUWBEUXTPNYOTYREV
      VESNYSYTEVVCVVFNUWCXPUEDVVHNCUWDTUWEVUJUWOVUOUWLAUXMBUYFUWFUWGUWIXRUWHUWJ
      RUWK $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b c d e $.  $d B a b c d e $.  $d N a b c d e $.

    $( If two sets are Diophantine, so is their union. $)
    diophun $p |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A u. B )
        e. ( Dioph ` N ) ) $=
      ( vb vd va vc ve cfv wcel cn0 wa cv co wceq cc0 cn wrex cab cz cdioph cun
      wi eldiophelnn0 c1 cfz cres cmap cmzp cvv cfn wn wss wb nnex jctr com cen
      ominf omex nnenom enfi mp2an mtbir elfznn ssriv eldioph2b anbi12d sylancl
      wbr pm3.2i reeanv cmul cmpt unab r19.43 andi nn0ssz zex mapss ax-mp sseli
      wo adantl weq fveq2 oveq12d eqid ovex fvmpt syl eqeq1d zsscn simplrl mzpf
      cc wf ffvelrn syl2anc sseldi simplrr mul0or bitr2d anbi2d rexbidva abbidv
      syl5bbr syl5eq simpl a1i wfn simprl ffn 3syl dffn5v sylib eqeltrrd simprr
      mzpmulmpt syl3anc eqeltrd uneq12 eleq1d syl5ibrcom syl5bir sylbid anabsi5
      eldioph2 rexlimdvva ) ACUAIZJZBYJJZABUBZYJJZYKCKJZYKYLLZYNUCACUDYOYPADMEM
      ZUECUFNZUGOZYQFMZIZPOZLZEKQUHNZRZDSZOZFQUIIZRZBYSYQGMZIZPOZLZEUUDRZDSZOZG
      UUHRZLZYNYOYOQUJJZLZQUKJZULZYRQUMZLZYPUURUNYOUUSUOUPUVBUVCUVAUQUKJZUSUQUJ
      JQUQURVJUVAUVEUNUTVAQUQUJVBVCVDFYRQYTCVEVFZVKUUTUVDLYKUUIYLUUQEDAQCFVGEDB
      QCGVGVHVIUURUUGUUPLZGUUHRFUUHRYOYNUUGUUPFGUUHUUHVLYOUVGYNFGUUHUUHYOYTUUHJ
      ZUUJUUHJZLZLZYNUVGUUFUUOUBZYJJUVKUVLYSYQHTQUHNZHMZYTIZUVNUUJIZVMNZVNZIZPO
      ZLZEUUDRZDSZYJUVKUVLUUEUUNWCZDSUWCUUEUUNDVOUVKUWDUWBDUWDUUCUUMWCZEUUDRUVK
      UWBUUCUUMEUUDVPUVKUWEUWAEUUDUWEYSUUBUULWCZLUVKYQUUDJZLZUWAYSUUBUULVQUWHUW
      FUVTYSUWHUVTUUAUUKVMNZPOZUWFUWHUVSUWIPUWHYQUVMJZUVSUWIOUWGUWKUVKUUDUVMYQK
      TUMUUDUVMUMVRKTQVSUOVTWAWBWDZHYQUVQUWIUVMUVRHEWEUVOUUAUVPUUKVMUVNYQYTWFUV
      NYQUUJWFWGUVRWHUUAUUKVMWIWJWKWLUWHUUAWPJUUKWPJUWJUWFUNUWHTWPUUAWMUWHUVMTY
      TWQZUWKUUATJUWHUVHUWMYOUVHUVIUWGWNYTQWOZWKUWLUVMTYQYTWRWSWTUWHTWPUUKWMUWH
      UVMTUUJWQZUWKUUKTJUWHUVIUWOYOUVHUVIUWGXAUUJQWOZWKUWLUVMTYQUUJWRWSWTUUAUUK
      XBWSXCXDXGXEXGXFXHUVKYOUUSUVCLZUVRUUHJZUWCYJJYOUVJXIUWQUVKUUSUVCUOUVFVKXJ
      UVKHUVMUVOVNZUUHJHUVMUVPVNZUUHJUWRUVKYTUWSUUHUVKYTUVMXKZYTUWSOUVKUVHUWMUX
      AYOUVHUVIXLZUWNUVMTYTXMXNHUVMYTXOXPUXBXQUVKUUJUWTUUHUVKUUJUVMXKZUUJUWTOUV
      KUVIUWOUXCYOUVHUVIXRZUWPUVMTUUJXMXNHUVMUUJXOXPUXDXQHUVOUVPQXSWSEDUVRQCYHX
      TYAUVGYMUVLYJAUUFBUUOYBYCYDYIYEYFWKYG $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b c d $.  $d B a b c d $.
    $( Diophantine sets are sets of tuples of natural numbers. $)
    eldiophss $p |- ( A e. ( Dioph ` B ) -> A C_ ( NN0 ^m ( 1 ... B ) ) ) $=
      ( vb vc va vd cfv wcel cn0 cv co wceq wa cn cmap wrex wss simpr rexlimdva
      ex cdioph c1 cfz cres cc0 cab cmzp eldioph3b vex weq eqeq1 anbi1d rexbidv
      elab elfznn ssriv nnex elmapssres mp3an23 ad2antlr eqeltrd adantrd syl5bi
      cvv ssrdv adantr eqsstrd imp sylbi ) ABUAGHBIHZACJZDJZUBBUCKZUDZLZVLEJZGU
      ELZMZDINOKZPZCUFZLZENUGGZPZMAIVMOKZQZDCABEUHVJWDWFVJWBWFEWCVJVPWCHMZWBWFW
      GWBMAWAWEWGWBRWGWAWEQWBWGFWAWEFJZWAHWHVNLZVQMZDVSPZWGWHWEHZVTWKCWHFUICFUJ
      ZVRWJDVSWMVOWIVQVKWHVNUKULUMUNWGWJWLDVSWGVLVSHZMZWIWLVQWOWIWLWOWIMWHVNWEW
      OWIRWNVNWEHZWGWIWNVMNQNVDHWPEVMNVPBUOUPUQVLINVMURUSUTVATVBSVCVEVFVGTSVHVI
      $.
      $( [10-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 3: construction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t u a b c d e f g h $.  $d M a b c d e f g h $.
    $d S t u a b c d e f g h $.
    $( Projecting a Diophantine set by removing a coordinate results in a
       Diophantine set. $)
    diophrex $p |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) /\ S e. ( Dioph ` M ) ) ->
        { t | E. u e. S t = ( u |` ( 1 ... N ) ) } e. ( Dioph ` N ) ) $=
      ( va vb vd ve vc cn0 wcel cfv cv cres wceq wrex cab wa wex cuz cdioph w3a
      c1 cfz co weq eqeq1 rexbidv reseq1 eqeq2d cbvrexv syl6bb cbvabv cmap cmzp
      cc0 cn eldioph3b simprbi 3ad2ant3 rexeq abbidv adantl rexab r19.41v exbii
      anbi1d rexcom4 anass vex resex anbi2d ceqsexv bitri ancom wss simpl2 3syl
      resabs1 syl5bb syl5bbr eldioph3 3ad2antl1 eqeltrd adantr ex rexlimdva mpd
      fzss2 syl5eqelr ) EKLZDEUAMLZCDUBMLZUCZBNZANZUDEUEUFZOZPZACQZBRFNZGNZWROZ
      PZGCQZFRZEUBMZXFXAFBFBUGZXFWPXDPZGCQXAXIXEXJGCXBWPXDUHUIXJWTGACGAUGXDWSWP
      XCWQWRUJUKULUMUNWOCHNZINZUDDUEUFZOZPZXLJNZMUQPZSZIKURUOUFZQZHRZPZJURUPMZQ
      ZXGXHLZWNWLYDWMWNDKLYDIHCDJUSUTVAWOYBYEJYCWOXPYCLZSZYBYEYGYBSXGXEGYAQZFRZ
      XHYBXGYIPYGYBXFYHFXEGCYAVBVCVDYGYIXHLYBYGYIXBXLWROZPZXQSZIXSQZFRZXHYGYHYM
      FYHXCXNPZXQSZIXSQZXESZGTZYGYMXTYQXEHGHGUGZXRYPIXSYTXOYOXQXKXCXNUHVHUIVEYS
      YPXESZIXSQZGTZYGYMUUBYRGYPXEIXSVFVGUUCUUAGTZIXSQYGYMUUAIGXSVIYGUUDYLIXSUU
      DXQXBXNWROZPZSZYGYLUUDYOXQXESZSZGTUUGUUAUUIGYOXQXEVJVGUUHUUGGXNXLXMIVKVLY
      OXEUUFXQYOXDUUEXBXCXNWRUJUKVMVNVOUUGUUFXQSYGYLXQUUFVPYGUUFYKXQYGUUEYJXBYG
      WMWRXMVQUUEYJPWLWMWNYFVREUDDWJXLWRXMVTVSUKVHWAWAUIWBWBWAVCWLWMYFYNXHLWNIF
      XPEWCWDWEWFWEWGWHWIWK $.
      $( [10-Oct-2014] $)
  $}

  ${
    $d N t a b c d e $.  $d A a b c d e $.  $d B a b $.

    $( This is the first of a number of theorems which allow sets to be proven
       Diophantine by syntactic induction, and models the correspondence
       between Diophantine sets and monotone existential first order logic.
       This first theorem shows that the zero set of an implicit polynomial is
       Diophantine. $)
    eq0rabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = 0 } e.
        ( Dioph ` N ) ) $=
      ( va vb vd cn0 wcel cz co cfv wa cc0 wceq crab cv ax-17 eqeq1d weq syl6eq
      c1 cfz cmap cmpt cmzp cres wrex cab cdioph wb wral hbmpt1 hbel wss nn0ssz
      hban zex ovex mapss ax-mp sseli adantl wf mzpf mptfcl syl2an adantll eqid
      imp fvmpt2 syl2anc eqcomd ralrimi rabbi sylib wel hbfv hbeq cbvrab df-rab
      fveq2 wfn nn0ex elmap biimpi ffn fnresdm 3syl eqeq2d equcom syl6bb anbi1d
      ex rexbiia ceqsrexbv bitr2i abbii cuz simpl nn0z syl adantr simpr eldioph
      uzid syl3anc eqeltrd ) CGHZAIUACUBJZUCJZBUDZXIUEKZHZLZBMNZAGXIUCJZOZDPZEP
      ZXIUFZNZXSXKKZMNZLZEXPUGZDUHZCUIKZXNXQXRXPHXRXKKZMNZLZDUHZYFXNXQYIDXPOZYK
      XNXQAPZXKKZMNZAXPOZYLXNXOYOUJZAXPUKXQYPNXNYQAXPXHXMAXHAQAFFXKXLAFXJBULZFP
      ZXLHAQUMUPXNYMXPHZYQXNYTLZBYNMUUAYNBUUAYMXJHZBIHZYNBNYTUUBXNXPXJYMGIUNXPX
      JUNUOGIXIUQUACUBURZUSUTVAZVBXMYTUUCXHXMXJIXKVCZUUBUUCYTXKXIVDUUEUUFUUBUUC
      AXJBIVEVIVFVGAXJBIXKXKVHVJVKVLRWMVMXOYOAXPVNVOYOYIADFXPYSXPHZAQUUGDQYODQA
      FFYHMAFXRXKYRFDVPAQVQYSMHAQVRADSYNYHMYMXRXKWARVSTYIDXPVTTYJYEDYEEDSZYCLZE
      XPUGYJYDUUIEXPXSXPHZYAUUHYCUUJYADESUUHUUJXTXSXRUUJXIGXSVCZXSXIWBXTXSNUUJU
      UKGXIXSWCUUDWDWEXIGXSWFXIXSWGWHWIDEWJWKWLWNYCYIEXRXPUUHYBYHMXSXRXKWARWOWP
      WQTXNXHCCWRKHZXMYFYGHXHXMWSXHUULXMXHCIHUULCWTCXEXAXBXHXMXCEDXKCCXDXFXG $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for equality of polynomial expressions.  Note
       that the two expressions need not be non-negative; only variables are so
       constrained. $)
    eqrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = B } e.
        ( Dioph ` N ) ) $=
      ( va cn0 wcel cz c1 cfz co cmap cmpt cfv wceq crab wa wb hbmpt1 cc cdioph
      cmzp w3a cmin cc0 wral ax-17 hbel hban zsscn mzpf ad2antrr wss nn0ssz zex
      cv wf ovex mapss ax-mp sseli adantl mptfcl sseldi ad2antlr subeq0 syl2anc
      bicomd ex ralrimi rabbi sylib 3adant1 simp1 mzpsubmpt eq0rabdioph eqeltrd
      sylc ) DFGZAHIDJKZLKZBMZVTUBNZGZAWACMZWCGZUCZBCOZAFVTLKZPZBCUDKZUEOZAWIPZ
      DUANZWDWFWJWMOZVSWDWFQZWHWLRZAWIUFWOWPWQAWIWDWFAAEEWBWCAEWABSEUPWCGAUGZUH
      AEEWEWCAEWACSWRUHUIWPAUPZWIGZWQWPWTQZWLWHXABTGCTGWLWHRXAHTBUJXAWAHWBUQZWS
      WAGZBHGWDXBWFWTWBVTUKULWTXCWPWIWAWSFHUMWIWAUMUNFHVTUOIDJURUSUTVAVBZAWABHV
      CVRVDXAHTCUJXAWAHWEUQZXCCHGWFXEWDWTWEVTUKVEXDAWACHVCVRVDBCVFVGVHVIVJWHWLA
      WIVKVLVMWGVSAWAWKMWCGZWMWNGVSWDWFVNWDWFXFVSABCVTVOVMAWKDVPVGVQ $.
      $( [10-Oct-2014] $)

    $( The null set is Diophantine. $)
    0dioph $p |- ( A e. NN0 -> (/) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c0 c1 cc0 wceq cfz co cmap crab cdioph cfv wral wne ax-1ne0
      wn df-ne cz mpbi rgenw rabeq0 mpbir cmpt cmzp cvv mzpconstmpt eq0rabdioph
      ovex 1z mp2an mpan2 syl5eqelr ) ACDZEFGHZBCFAIJZKJZLZAMNZUSEHUPRZBUROVABU
      RFGPVAQFGSUAUBUPBURUCUDUOBTUQKJFUEUQUFNDZUSUTDUQUGDFTDVBFAIUJUKBFUQUHULBF
      AUIUMUN $.
      $( [10-Oct-2014] $)

    $( The "universal" set (as large as possible given ~ eldiophss ) is
       Diophantine. $)
    vdioph $p |- ( A e. NN0 -> ( NN0 ^m ( 1 ... A ) ) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c1 cfz co cmap cc0 wceq crab cdioph wral eqid1 rgenw rabid2
      cfv mpbir cz cmpt cmzp cvv ovex 0z mzpconstmpt mp2an eq0rabdioph syl5eqel
      mpan2 ) ACDZCEAFGZHGZIIJZBULKZALQZULUNJUMBULMUMBULINOUMBULPRUJBSUKHGITUKU
      AQDZUNUODUKUBDISDUPEAFUCUDBIUKUEUFBIAUGUIUH $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for conjunctions. $)
    anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph /\ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cin inrab diophin syl5eqelr
      ) ACEFDGHIHZJZDKLZMBCSJZUAMNABNCSJTUBOUAABCSPTUBDQR $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for disjunctions. $)
    orrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph \/ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cun unrab diophun syl5eqelr
      wo ) ACEFDGHIHZJZDKLZMBCTJZUBMNABSCTJUAUCOUBABCTPUAUCDQR $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for conjunctions. $)
    3anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. (
        NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1
        ... N ) ) | ( ph /\ ps /\ ch ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel w3a wa wb cv df-3an anrabdioph
      a1i rabbiia sylan syl5eqel 3impa ) ADFGEHIJIZKELMZNZBDUFKUGNZCDUFKUGNZABC
      OZDUFKZUGNUHUIPZUJPULABPZCPZDUFKZUGUKUODUFUKUOQDRUFNABCSUAUBUMUNDUFKUGNUJ
      UPUGNABDETUNCDETUCUDUE $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for disjunctions. $)
    3orrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. (
        NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1
        ... N ) ) | ( ph \/ ps \/ ch ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel w3o wa wo wb cv orrabdioph a1i
      df-3or rabbiia sylan syl5eqel 3impa ) ADFGEHIJIZKELMZNZBDUGKUHNZCDUGKUHNZ
      ABCOZDUGKZUHNUIUJPZUKPUMABQZCQZDUGKZUHULUPDUGULUPRDSUGNABCUBUAUCUNUODUGKU
      HNUKUQUHNABDETUOCDETUDUEUF $.
      $( [10-Oct-2014] $)

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 4 miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A nonempty finite range of integers contains its end point. $)
  elfz1end $p |- ( A e. NN <-> A e. ( 1 ... A ) ) $=
    ( cn wcel c1 cfz co cuz cfv elnnuz biimpi cz nnz uzid eluzfz syl2anc elfznn
    syl impbii ) ABCZADAEFCZSADGHCZAAGHCZTSUAAIJSAKCUBALAMQADANOAAPR $.
    $( [10-Oct-2014] $)

  ${
    $d A c $.  $d B c $.  $d C b $.  $d a c $.  $d b c $.  $d C a $.
    2sbcrex.1 $e |- A e. _V $.
    2sbcrex.2 $e |- B e. _V $.
    $( Exchange an existential quantifier with two substitutions. $)
    2sbcrex $p |- ( [ A / a ] [ B / b ] E. c e. C ph <-> E. c e. C [ A / a ] [
        B / b ] ph ) $=
      ( wrex wsbc cvv wcel wb sbcrexg ax-mp sbcbii bitri ) AGDJFCKZEBKZAFCKZGDJ
      ZEBKZUAEBKGDJZBLMZTUCNHSUBEBLCLMSUBNIAFGCDLOPQPUEUCUDNHUAEGBDLOPR $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a b $.  $d a c $.
    $( Exchange a substitution with two existentials. $)
    sbc2rexg $p |- ( A e. V -> ( [ A / a ] E. b e. B E. c e. C ph <-> E. b e. B
        E. c e. C [ A / a ] ph ) ) $=
      ( wcel cvv wrex wsbc wb elex sbcrexg rexbidv bitrd syl ) BEIBJIZAHDKZGCKF
      BLZAFBLHDKZGCKZMBENSUATFBLZGCKUCTFGBCJOSUDUBGCAFHBDJOPQR $.
      $( [11-Oct-2014] $)

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a d $.  $d a e $.
    $( Exchange a substitution with 4 existentials. $)
    sbc4rexg $p |- ( A e. V -> ( [ A / a ] E. b e. B E. c e. C E. d e. D E. e
        e. E ph <-> E. b e. B E. c e. C E. d e. D E. e e. E [ A / a ] ph ) ) $=
      ( wcel cvv wrex wsbc wb elex sbc2rexg 2rexbidv bitrd syl ) BHMBNMZAFGOLEO
      ZKDOJCOIBPZAIBPFGOLEOZKDOJCOZQBHRUCUEUDIBPZKDOJCOUGUDBCDNIJKSUCUHUFJKCDAB
      EGNILFSTUAUB $.
      $( [11-Oct-2014] $)
  $}

  ${
    sbcbiii.1 $e |- A e. _V $.
    sbcbiii.2 $e |- ( ph <-> ps ) $.
    $( Fully inferenced rewriting under an explicit substitution. $)
    sbcbiii $p |- ( [ A / a ] ph <-> [ A / a ] ps ) $=
      ( cvv wcel wsbc wb sbcbii ax-mp ) CGHADCIBDCIJEABDCGFKL $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a c $.  $d a b $.
    $( also my first direct use of ax-4 $)
    $( Rotate a sequence of three explicit substitutions, closed theorem. $)
    sbcrot3g $p |- ( ( A e. D /\ B e. E /\ A. b C e. F ) -> ( [ A / a ] [ B / b
        ] [ C / c ] ph <-> [ B / b ] [ C / c ] [ A / a ] ph ) ) $=
      ( wcel cvv wal wsbc wb elex alimi w3a sbccomg 3adant3 wa simp2 ax-17 hba1
      3simpb hban ax-4 sylan2 sbcbid syl2anc bitrd syl3an ) BEKBLKZCFKCLKZDGKZI
      MDLKZIMZAJDNZICNHBNZAHBNJDNZICNZOBEPCFPUOUPIDGPQUMUNUQRZUSURHBNZICNZVAUMU
      NUSVDOUQURHIBCLLSTVBUMUQUAZUNVDVAOUMUNUQUEUMUNUQUBVEVCUTICLUMUQIUMIUCUPIU
      DUFUQUMUPVCUTOUPIUGAHJBDLLSUHUIUJUKUL $.
      $( [11-Oct-2014] $)

    sbcrot3.1 $e |- A e. _V $.
    sbcrot3.2 $e |- B e. _V $.
    sbcrot3.3 $e |- C e. _V $.
    $( Rotate a sequence of three explicit substitutions.  Substituted values
       must be manifest sets. $)
    sbcrot3 $p |- ( [ A / a ] [ B / b ] [ C / c ] ph <-> [ B / b ] [ C / c ] [
        A / a ] ph ) $=
      ( cvv wcel wal wsbc wb ax-gen sbcrot3g mp3an ) BKLCKLDKLZFMAGDNFCNEBNAEBN
      GDNFCNOHISFJPABCDKKKEFGQR $.
      $( [11-Oct-2014] $)

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a e $.  $d a d $.
    sbcrot5.4 $e |- D e. _V $.
    sbcrot5.5 $e |- E e. _V $.
    $( Rotate a sequence of five explicit substitutions.  Substituted values
       must be manifest sets. $)
    sbcrot5 $p |- ( [ A / a ] [ B / b ] [ C / c ] [ D / d ] [ E / e ] ph <-> [
        B / b ] [ C / c ] [ D / d ] [ E / e ] [ A / a ] ph ) $=
      ( wsbc sbcrot3 sbcbiii bitri ) AFGQKEQZJDQICQHBQUAHBQZJDQZICQAHBQFGQKEQZJ
      DQZICQUABCDHIJLMNRUCUECIMUBUDDJNABEGHKFLOPRSST $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d A a c $.  $d A a b $.  $d C a c $.
    sbccomieg.1 $e |- ( a = A -> B = C ) $.
    $( Commute two explicit substitutions, using an implicit substitution to
       rewrite the exiting substitution. $)
    sbccomieg $p |- ( ( A e. V /\ C e. W ) -> ( [ A / a ] [ B / b ] ph <-> [ C
        / b ] [ A / a ] ph ) ) $=
      ( vc wcel wa cvv wsbc wal wi cv wceq wb ax-17 elex adantr hbsbc1g hbsbcgd
      adantl a17d alrimiv syl2anc dfsbcq syl sbceq1a sbcbidv ancoms ex sbciegft
      bitrd syl3anc ) BEKZDFKZLZBMKZAGBNZHDNZVCGOPZGOZGQBRZAHCNZVCSZPZGOZVGGBNV
      CSURVAUSBEUAUBZUTVADMKZVEVKUSVLURDFUAUEZVAVLLVDGVAVBGHJDMVAGTVAHTVAJQZDKG
      UFAGJBMVNBKGTUCUDUGUHUTVLVJVMVLVIGVLVFVHVLVFLZVGAHDNZVCVOCDRZVGVPSVFVQVLI
      UEAHCDUIUJVFVLVPVCSVFAVBHDMAGBUKULUMUPUNUGUJVGVCGBMUOUQ $.
      $( [11-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 4: Quantification
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t u v a b c d e $.  $d M t u v a b c d e $.  $d ph u v a b c d e $.
    $d ps t a b c d e $.  $d ch v a b c d e $.
    rexrabdioph.1 $e |- M = ( N + 1 ) $.
    rexrabdioph.2 $e |- ( v = ( t ` M ) -> ( ps <-> ch ) ) $.
    rexrabdioph.3 $e |- ( u = ( t |` ( 1 ... N ) ) -> ( ch <-> ph ) ) $.

    $( TODO: something very wrong with this proof, should be a trivial definition check? $)
    $( Diophantine set builder for existential quantification. $)
    rexrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | ph } e. (
        Dioph ` M ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ps } e. (
        Dioph ` N ) ) $=
      ( va vb vc cn0 wcel wa wceq wsbc wb c1 cfz cmap crab cdioph cfv wrex cres
      co cv cab wsb df-rab sbequ cbvrexv anbi2i r19.42v bitr4i cop simpll simpr
      csn cun simplr mapfzcons syl3anc adantrr mapfzcons2 eqcomd dfsbcq syl cvv
      mapfzcons1 sbcbidv mpan2 bitrd biimpd fveq1 reseq1 eqeq2d anbi12d rcla4ev
      fvex impr syl12anc ex rexlimdva wf ovex elmapi cn caddc syl5eqel elfz1end
      nn0p1nn sylib ffvelrn syl2anr adantr simprr mapfzcons1cl eqeltrd ad2antll
      mpan simprl mpbird anbi2d impbid syl5bb abbidv syl5eq ax-17 hbs1 hbsb weq
      hbrex sbequ12 rexbidv cbvrexsv syl6bb cbvrab abbii 3eqtr4g resex sylan9bb
      rexrab vex sbc2ie a1i rabbiia rexeq ax-mp syl6eq simpl nn0z uzid peano2uz
      cuz cz 3syl diophrex ) HOPZAFOUAGUBUIZUCUIZUDZGUEUFPZQZBDOUGZEOUAHUBUIZUC
      UIZUDZLUJZMUJZUUIUHZRZMUUEUGZLUKZHUEUFZUUBUUKUUQRUUFUUBUUKUUOMBEFUJZUUIUH
      ZSZDGUUSUFZSZFUUDUDZUGZLUKZUUQUUBBELULZDMULZMOUGZLUUJUDZBEUUNSZDGUUMUFZSZ
      UUOQZMUUDUGZLUKZUUKUVFUUBUVJUULUUJPZUVIQZLUKUVPUVILUUJUMUUBUVRUVOLUVRUVQU
      VGDNULZQZNOUGZUUBUVOUVRUVQUVSNOUGZQUWAUVIUWBUVQUVHUVSMNOUVGMNDUNUOUPUVQUV
      SNOUQURUUBUWAUVOUUBUVTUVONOUUBNUJZOPZQZUVTUVOUWEUVTQUULGUWCUSVBVCZUUDPZBE
      UWFUUIUHZSZDGUWFUFZSZUULUWHRZUVOUWEUVQUWGUVSUWEUVQQZUUBUVQUWDUWGUUBUWDUVQ
      UTZUWEUVQVAZUUBUWDUVQVDZUULOUWCGHIVEVFVGUWEUVQUVSUWKUWMUVSUWKUWMUVSUVGDUW
      JSZUWKUWMUWCUWJRUVSUWQTUWMUWJUWCUWMUUBUVQUWDUWJUWCRUWNUWOUWPUULOUWCGHIVHV
      FVIUVGDUWCUWJVJVKUWMUWJVLPZUWQUWKTGUWFWCZUWMUVGUWIDUWJVLUWMUWLUVGUWITUWMU
      WHUULUWMUUBUVQUWDUWHUULRUWNUWOUWPUULOUWCGHIVMVFVIZBEUULUWHVJVKVNVOVPVQWDU
      WEUVQUWLUVSUWTVGUVNUWKUWLQMUWFUUDUUMUWFRZUVMUWKUUOUWLUXAUVMUVKDUWJSZUWKUX
      AUVLUWJRUVMUXBTGUUMUWFVRUVKDUVLUWJVJVKUXAUWRUXBUWKTUWSUXAUVKUWIDUWJVLUXAU
      UNUWHRUVKUWITUUMUWFUUIVSZBEUUNUWHVJVKVNVOVPUXAUUNUWHUULUXCVTWAWBWEWFWGUUB
      UVNUWAMUUDUUBUUMUUDPZQZUVNUWAUXEUVNQZUVLOPZUVQUVGDUVLSZUWAUXEUXGUVNUXDUUC
      OUUMWHZGUUCPZUXGUUBUUCVLPUXDUXIUAGUBWIUUMOUUCWJXDUUBGWKPUXJUUBGHUAWLUIZWK
      IHWOWMGWNWPUUCOGUUMWQWRWSUXFUULUUNUUJUXEUVMUUOWTUXEUUNUUJPUVNUUMOGHIXAWSX
      BUXFUXHUVMUXEUVMUUOXEUUOUXHUVMTZUXEUVMUUOUVLVLPZUXLGUUMWCZUUOUVGUVKDUVLVL
      BEUULUUNVJVNVOXCXFUVTUVQUXHQNUVLOUWCUVLRUVSUXHUVQUVGDUWCUVLVJXGWBWEWFWGXH
      XIXJXKUUHUVIELMUUJUUMUUJPZEXLUXOLXLUUHLXLUVHEMOUUMOPEXLUVGDMEBELXMXNXPELX
      OZUUHUVGDOUGUVIUXPBUVGDOBELXQXRUVGDMOXSXTYAUVEUVOLUVCUVMUUOFMUUDFMXOZUVCU
      VADUVLSZUVMUXQUVBUVLRUVCUXRTGUUSUUMVRUVADUVBUVLVJVKUXQUXMUXRUVMTUXNUXQUVA
      UVKDUVLVLUXQUUTUUNRUVAUVKTUUSUUMUUIVSBEUUTUUNVJVKVNVOVPYFYBYCUVEUUPLUVDUU
      ERUVEUUPTUVCAFUUDUVCATUUSUUDPBADEUVBUUTGUUSWCUUSUUIFYGYDDUJUVBRBCEUJUUTRA
      JKYEYHYIYJUUOMUVDUUEYKYLYBYMWSUUGUUBGHYRUFZPZUUFUUQUURPUUBUUFYNUUBUXTUUFU
      UBGUXKUXSIUUBHYSPHUXSPUXKUXSPHYOHYPHHYQYTWMWSUUBUUFVAMLUUEGHUUAVFXB $.
      $( [10-Oct-2014] $)
  $}

  ${
    $d G a b c d e f t u v w x y z p q $.
    $d H a b c d e f t u v w x y z p q $.
    $d I a b c d e f t u v w x y z p q $.
    $d J a b c d e f t u v w x y z p q $.
    $d K a b c d e f t u v w x y z p q $.
    $d L a b c d e f t u v w x y z p q $.
    $d M a b c d e f t u v w x y z p q $.
    $d N a b c d e f t u v w x y z p q $.  $d ph a b c d e f t $.
    rexfrabdioph.1 $e |- M = ( N + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution. $)
    rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | [ ( t |`
        ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] ph } e. ( Dioph ` M ) ) -> { u e.
        ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cv cfv wsbc co crab wrex wsb ax-17 c1 cfz cres cdioph
      cmap wa hbsb3 hbrex weq sbceq1a cbvrex rexbidv syl5bb cbvrab wceq cvv vex
      wb dfsbcq sbcbidv mpan2 rexrabdioph syl5eqel ) FKLABEDMZNZOZCVDUAFUBPZUCZ
      OZDKUAEUBPUEPQEUDNLUFABKRZCKVGUEPZQABHSZCISZHKRZIVKQFUDNVJVNCIJVKJMVKLZCT
      VOITVJITVMCHKHMZKLCTVLCIVLITUGUHVJVLHKRCIUIZVNAVLBHKAHTZABHVRUGABVPUJUKVQ
      VLVMHKVLCIMZUJULUMUNVIVMVFCISZHIDEFGVPVEUOZVSUPLVMVTURIUQWAVLVFCVSUPABVPV
      EUSUTVAVFCVSVHUSVBVC $.
      $( [11-Oct-2014] $)

    rexfrabdioph.2 $e |- L = ( M + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables. $)
    2rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... L ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] ph } e. (
        Dioph ` L ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e.
        NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc c1 cfz co wb cvv cv cres cmap crab cdioph wrex vex
      wa resex fvex 2sbcrex a1i rabbiia caddc peano2nn0 syl5eqel adantr sbcrot3
      sbcbii ax-mp reseq1 sbccomieg mp2an wss wceq fzssp1 oveq2i resabs1 dfsbcq
      syl6sseqr wal ax-gen fveq1 sbcco3g cn nn0p1nn elfz1end sylib fvres syl5bb
      sbcbidv mpan2 syl5rbb rabbidv eleq1d biimpa rexfrabdioph syl2anc syldan
      3syl bitrd ) HLMZABFEUAZNZOZCGWMNZOZDWMPHQRZUBZOZELPFQRUCRZUDZFUENZMZABLU
      FZCGKUAZNZODXFWRUBZOZKLPGQRZUCRZUDZGUENZMXECLUFDLWRUCRUDHUENMWLXDUHZXLACX
      GODXHOZBLUFZKXKUDZXMXIXPKXKXIXPSXFXKMAXHXGLDCBXFWRKUGUIZGXFUJZUKULUMXNGLM
      ZXOBWNOZKWMXJUBZOZEXAUDZXCMZXQXMMWLXTXDWLGHPUNRZLIHUOUPUQWLXDYEWLXBYDXCWL
      WTYCEXAYCWOCXGOZDXHOZKYBOZWLWTYBTMZYCYISWMXJEUGZUIZYAYHKYBTAWNXHXGBDCFWMU
      JXRXSURUSUTYIYGKYBOZDYBWRUBZOZWLWTYJYNTMYIYOSYLYBWRYLUIYGYBXHYNTTKDXFYBWR
      VAVBVCWLYOYMDWSOZWTWLWRXJVDYNWSVEYOYPSWLWRPYFQRXJPHLVFGYFPQIVGVJWMWRXJVHY
      MDYNWSVIWJWLWSTMYPWTSWMWRYKUIWLYMWQDWSTYMWOCGYBNZOZWLWQYJXGTMZKVKYMYRSYLY
      SKXSVLWOKCYBXGYQTTGXFYBVMVNVCWLGXJMZYQWPVEYRWQSWLGVOMYTWLGYFVOIHVPUPGVQVR
      GXJWMVSWOCYQWPVIWJVTWAWBWKVTWCWDWEWFXOBKEFGJWGWHUPXECDKGHIWGWI $.
      $( [11-Oct-2014] $)

    rexfrabdioph.3 $e |- K = ( L + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables. $)
    3rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... K ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] ph } e. ( Dioph ` K ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 ph
        } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc co cvv cv c1 cfz cres cmap crab cdioph wrex wa vex
      wb resex fvex sbc2rexg ax-mp sbcbiii bitri rabbiia caddc nn0p1nn syl5eqel
      a1i cn nnnn0 syl adantr sbcrot3 reseq1 sbccomieg mp2an wceq fzssp1 oveq2i
      wss syl6sseqr resabs1 dfsbcq wal ax-gen fveq1 elfz1end sylib fvres syl5bb
      sbcco3g sbcbidv mpan2 bitrd syl5bbr rabbidv biimpar 2rexfrabdioph syl2anc
      eleq1d rexfrabdioph syldan ) JOPZABGFUAZQZRCHWRQZRZDIWRQZRZEWRUBJUCSZUDZR
      ZFOUBGUCSUESZUFZGUGQZPZABOUHCOUHZDINUAZQZRZEXLXDUDZRZNOUBIUCSZUESZUFZIUGQ
      ZPXKDOUHEOXDUESUFJUGQPWQXJUIZXSADXMRZEXORZBOUHCOUHZNXRUFZXTXPYDNXRXPYDUKX
      LXRPXPYBBOUHCOUHZEXORZYDXNYFXOEXLXDNUJULZXMTPZXNYFUKIXLUMZAXMOOTDCBUNUOUP
      XOTPYGYDUKYHYBXOOOTECBUNUOUQVBURYAIOPZYCBWSRCWTRZNWRXQUDZRZFXGUFZXIPZYEXT
      PWQYKXJWQIVCPZYKWQIJUBUSSZVCKJUTVAZIVDVEVFWQYPXJWQYOXHXIWQYNXFFXGYNXADXMR
      ZEXORZNYMRZWQXFUUAYLYMNWRXQFUJZULZUUAYBBWSRCWTRZEXORYLYTUUEXOEYHAXMWTWSDC
      BYJHWRUMZGWRUMZVGUPYBXOWTWSECBYHUUFUUGVGUQUPUUBYTNYMRZEYMXDUDZRZWQXFYMTPZ
      UUITPUUBUUJUKUUDYMXDUUDULYTYMXOUUITTNEXLYMXDVHVIVJWQUUJUUHEXERZXFWQUUIXEV
      KZUUJUULUKWQXDXQVNUUMWQXDUBYRUCSXQUBJOVLIYRUBUCKVMVOWRXDXQVPVEUUHEUUIXEVQ
      VEWQXETPUULXFUKWRXDUUCULWQUUHXCEXETUUHXADIYMQZRZWQXCUUKYINVRUUHUUOUKUUDYI
      NYJVSXANDYMXMUUNTTIXLYMVTWEVJWQUUNXBVKZUUOXCUKWQIXQPZUUPWQYQUUQYSIWAWBIXQ
      WRWCVEXADUUNXBVQVEWDWFWGWHWDWIWJWNWKYCBCNFGHILMWLWMVAXKDENIJKWOWP $.
      $( [17-Oct-2014] $)

    rexfrabdioph.4 $e |- J = ( K + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, 4 variables. $)
    4rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... J ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] [ ( t ` J ) / y ] ph } e. ( Dioph ` J ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E.
        y e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( cn0 wcel wsbc cvv va cv cfv c1 cfz co cres cmap crab cdioph wrex wa vex
      wb resex fvex 2sbcrex rexbii bitri sbcbii ax-mp sbcrexg a1i rabbiia caddc
      cn nn0p1nn syl5eqel peano2nn nnnn0 adantr sbcrot3 bitr3i reseq1 sbccomieg
      syl mp2an wceq fzssp1 oveq2i syl6sseqr ovex eqeltri eqcomi sseqtri syl6ss
      wss resabs1 dfsbcq 3syl fveq1 elfz1end sylib sseldi ax-gen sbcco3g syl5bb
      fvres wal sbcbidv mpan2 bitrd rabbidv eleq1d biimpar 2rexfrabdioph syldan
      syl2anc ) LQRZACHGUBZUCZSZBIXJUCZSZDJXJUCZSZEKXJUCZSZFXJUDLUEUFZUGZSZGQUD
      HUEUFUHUFZUIZHUJUCZRZACQUKZBQUKZDJUAUBZUCZSEKYHUCZSZFYHXSUGZSZUAQUDJUEUFZ
      UHUFZUIZJUJUCZRYGDQUKEQUKFQXSUHUFUILUJUCRXIYEULZYPADYISEYJSZFYLSZCQUKZBQU
      KZUAYOUIZYQYMUUBUAYOYMUUBUNYHYORYMYSCQUKZBQUKZFYLSZUUBYLTRZYMUUFUNYHXSUAU
      MUOZYKUUEFYLTYKYFDYISEYJSZBQUKUUEYFYJYIQEDBKYHUPZJYHUPZUQUUIUUDBQAYJYIQED
      CUUJUUKUQURUSUTVAUUFUUDFYLSZBQUKZUUBUUGUUFUUMUNUUHUUDFBYLQTVBVAUULUUABQUU
      GUULUUAUNUUHYSFCYLQTVBVAURUSUSVCVDYRJQRZYTCXKSBXMSZUAXJYNUGZSZGYBUIZYDRZU
      UCYQRXIUUNYEXIJVFRZUUNXIJKUDVEUFZVFNXIKVFRZUVAVFRXIKLUDVEUFZVFMLVGVHZKVIV
      PVHZJVJVPVKXIUUSYEXIUURYCYDXIUUQYAGYBUUQXNDYISZEYJSZFYLSZUAUUPSZXIYAUUPTR
      ZUUQUVIUNXJYNGUMZUOZUUOUVHUAUUPTUUOYSCXKSZBXMSZFYLSZUVHYSYLXMXKFBCUUHIXJU
      PZHXJUPZVLUUGUVOUVHUNUUHUVNUVGFYLTUVNXLDYISEYJSZBXMSZUVGXMTRUVNUVSUNUVPUV
      MUVRBXMTAXKYJYICEDUVQUUJUUKVLUTVAXLXMYJYIBEDUVPUUJUUKVLUSUTVAVMUTVAUVIUVG
      UAUUPSZFUUPXSUGZSZXIYAUVJUWATRUVIUWBUNUVLUUPXSUVLUOUVGUUPYLUWATTUAFYHUUPX
      SVNVOVQXIUWBUVTFXTSZYAXIXSYNWGUWAXTVRUWBUWCUNXIXSUDKUEUFZYNXIXSUDUVCUEUFU
      WDUDLQVSKUVCUDUEMVTWAUWDUDUVAUEUFZYNKTRUWDUWEWGKUVCTMLUDVEWBWCUDKTVSVAUVA
      JUDUEJUVANWDVTWEZWFXJXSYNWHUVTFUWAXTWIWJXIXTTRUWCYAUNXJXSUVKUOXIUVTXRFXTT
      UVTUVFUAUUPSZEKUUPUCZSZXIXRUVJUWHTRUVTUWIUNUVLKUUPUPUVFUUPYJUWHTTUAEKYHUU
      PWKVOVQXIUWIUWGEXQSZXRXIKYNRUWHXQVRUWIUWJUNXIUWDYNKUWFXIUVBKUWDRUVDKWLWMW
      NKYNXJWRUWGEUWHXQWIWJXIXQTRUWJXRUNKXJUPXIUWGXPEXQTUWGXNDJUUPUCZSZXIXPUVJY
      ITRZUAWSUWGUWLUNUVLUWMUAUUKWOXNUADUUPYIUWKTTJYHUUPWKWPVQXIJYNRZUWKXOVRUWL
      XPUNXIUUTUWNUVEJWLWMJYNXJWRXNDUWKXOWIWJWQWTXAXBWQWTXAXBWQWQXCXDXEYTCBUAGH
      IJOPXFXHVHYGDEFUAJKLMNXFXG $.
      $( [11-Oct-2014] $)

    rexfrabdioph.5 $e |- I = ( J + 1 ) $.
    rexfrabdioph.6 $e |- H = ( I + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, 6 variables. $)
    6rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... H ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] [ ( t ` J ) / y ] [ ( t ` I ) / z ] [ ( t ` H ) / p ] ph } e. (
        Dioph ` H ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E.
        y e. NN0 E. z e. NN0 E. p e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cv cfv wsbc c1 cfz co cres cmap crab cdioph wa wb vex resex
      wrex fvex cvv sbc4rexg ax-mp sbcbiii bitri rabbiia caddc nn0p1nn syl5eqel
      a1i cn peano2nn syl nnnn0 adantr sbcrot5 reseq1 sbccomieg wss wceq fzssp1
      mp2an oveq2i syl6sseqr eqeltri syl6ss resabs1 dfsbcq fveq1 elfz1end sylib
      ovex sseldi fvres wal ax-gen sbcco3g syl5bb sbcbidv mpan2 syl5bbr rabbidv
      3syl bitrd eleq1d biimpar 4rexfrabdioph syl2anc 2rexfrabdioph syldan ) OU
      DUEZAPIHUFZUGZUHDJXMUGZUHCKXMUGZUHBLXMUGZUHZEMXMUGZUHZFNXMUGZUHZGXMUIOUJU
      KZULZUHZHUDUIIUJUKUMUKZUNZIUOUGZUEZAPUDUTDUDUTCUDUTBUDUTZEMUCUFZUGZUHZFNY
      KUGZUHZGYKYCULZUHZUCUDUIMUJUKZUMUKZUNZMUOUGZUEYJEUDUTFUDUTGUDYCUMUKUNOUOU
      GUEXLYIUPZYTAEYLUHZFYNUHZGYPUHZPUDUTDUDUTCUDUTBUDUTZUCYSUNZUUAYQUUFUCYSYQ
      UUFUQYKYSUEYQUUDPUDUTDUDUTCUDUTBUDUTZGYPUHZUUFYOUUHYPGYKYCUCURUSZYOUUCPUD
      UTDUDUTCUDUTBUDUTZFYNUHZUUHYMUUKYNFNYKVAZYLVBUEZYMUUKUQMYKVAZAYLUDUDUDPUD
      VBEBCDVCVDVEYNVBUEUULUUHUQUUMUUCYNUDUDUDPUDVBFBCDVCVDVFVEYPVBUEUUIUUFUQUU
      JUUDYPUDUDUDPUDVBGBCDVCVDVFVKVGUUBMUDUEZUUEPXNUHDXOUHCXPUHBXQUHZUCXMYRULZ
      UHZHYFUNZYHUEZUUGUUAUEXLUUPYIXLMVLUEZUUPXLMNUIVHUKZVLRXLNVLUEZUVCVLUEXLNO
      UIVHUKZVLQOVIVJZNVMVNVJZMVOVNVPXLUVAYIXLUUTYGYHXLUUSYEHYFUUSXREYLUHZFYNUH
      ZGYPUHZUCUURUHZXLYEUVJUUQUURUCXMYRHURZUSZUVJUUDPXNUHDXOUHCXPUHBXQUHZGYPUH
      UUQUVIUVNYPGUUJUVIUUCPXNUHDXOUHCXPUHBXQUHZFYNUHUVNUVHUVOYNFUUMAYLXQXPXOPX
      NEBCDUUOLXMVAZKXMVAZJXMVAZIXMVAZVQVEUUCYNXQXPXOPXNFBCDUUMUVPUVQUVRUVSVQVF
      VEUUDYPXQXPXOPXNGBCDUUJUVPUVQUVRUVSVQVFVEUVKUVIUCUURUHZGUURYCULZUHZXLYEUU
      RVBUEZUWAVBUEUVKUWBUQUVMUURYCUVMUSUVIUURYPUWAVBVBUCGYKUURYCVRVSWCXLUWBUVT
      GYDUHZYEXLYCYRVTUWAYDWAUWBUWDUQXLYCUINUJUKZYRXLYCUIUVEUJUKUWEUIOUDWBNUVEU
      IUJQWDWENVBUEZUWEYRVTNUVEVBQOUIVHWMWFUWFUWEUIUVCUJUKYRUINVBWBMUVCUIUJRWDW
      EVDZWGXMYCYRWHUVTGUWAYDWIXDXLYDVBUEUWDYEUQXMYCUVLUSXLUVTYBGYDVBUVTUVHUCUU
      RUHZFNUURUGZUHZXLYBUWCUWIVBUEUVTUWJUQUVMNUURVAUVHUURYNUWIVBVBUCFNYKUURWJV
      SWCXLUWJUWHFYAUHZYBXLNYRUEUWIYAWAUWJUWKUQXLUWEYRNUWGXLUVDNUWEUEUVFNWKWLWN
      NYRXMWOUWHFUWIYAWIXDXLYAVBUEUWKYBUQNXMVAXLUWHXTFYAVBUWHXREMUURUGZUHZXLXTU
      WCUUNUCWPUWHUWMUQUVMUUNUCUUOWQXRUCEUURYLUWLVBVBMYKUURWJWRWCXLMYRUEZUWLXSW
      AUWMXTUQXLUVBUWNUVGMWKWLMYRXMWOXREUWLXSWIXDWSWTXAXEWSWTXAXEWSXBXCXFXGUUED
      PCBUCHIJKLMSTUAUBXHXIVJYJEFGUCMNOQRXJXK $.
      $( [11-Oct-2014] $)

    rexfrabdioph.7 $e |- G = ( H + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, 7 variables. $)
    7rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... G ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] [ ( t ` J ) / y ] [ ( t ` I ) / z ] [ ( t ` H ) / p ] [ ( t ` G )
        / q ] ph } e. ( Dioph ` G ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E.
        y e. NN0 E. z e. NN0 E. p e. NN0 E. q e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cv cfv wsbc c1 cfz co cres cmap crab cdioph wa wb vex resex
      wrex cvv fvex sbc2rexg ax-mp sbc4rexg 2rexbii bitri sbcbiii rabbiia caddc
      a1i cn nn0p1nn syl5eqel nnnn0 syl adantr sbcrot3 sbcrot5 reseq1 sbccomieg
      mp2an wss fzssp1 oveq2i syl6sseqr resabs1 dfsbcq wal ax-gen fveq1 sbcco3g
      wceq sylib fvres syl5bb sbcbidv mpan2 bitrd syl5bbr rabbidv 6rexfrabdioph
      elfz1end eleq1d biimpar syl2anc rexfrabdioph syldan ) PUGUHZAQIHUIZUJZUKR
      JXMUJZUKDKXMUJZUKCLXMUJZUKZBMXMUJZUKENXMUJZUKZFOXMUJZUKZGXMULPUMUNZUOZUKZ
      HUGULIUMUNUPUNZUQZIURUJZUHZAQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZFOUFUIZUJZUKZ
      GYMYDUOZUKZUFUGULOUMUNZUPUNZUQZOURUJZUHYLFUGVCGUGYDUPUNUQPURUJUHXLYJUSZYT
      AFYNUKZGYPUKZQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZUFYSUQZUUAYQUUFUFYSYQUUFUTYM
      YSUHYQUUCQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZGYPUKZUUFYOUUIYPGYMYDUFVAVBZYOYK
      FYNUKZBUGVCEUGVCZUUIYNVDUHZYOUUMUTOYMVEZYKYNUGUGVDFEBVFVGUULUUHEBUGUGUUNU
      ULUUHUTUUOAYNUGUGUGQUGVDFCDRVHVGVIVJVKUUJUUHGYPUKZBUGVCEUGVCZUUFYPVDUHZUU
      JUUQUTUUKUUHYPUGUGVDGEBVFVGUUPUUEEBUGUGUURUUPUUEUTUUKUUCYPUGUGUGQUGVDGCDR
      VHVGVIVJVJVNVLUUBOUGUHZUUDQXNUKRXOUKDXPUKCXQUKZBXSUKZEXTUKZUFXMYRUOZUKZHY
      GUQZYIUHZUUGUUAUHXLUUSYJXLOVOUHZUUSXLOPULVMUNZVOSPVPVQZOVRVSVTXLUVFYJXLUV
      EYHYIXLUVDYFHYGUVDYAFYNUKZGYPUKZUFUVCUKZXLYFUVKUVBUVCUFXMYRHVAZVBZUVKXRFY
      NUKZGYPUKZBXSUKZEXTUKZUVBUVKUVOBXSUKEXTUKZGYPUKUVRUVJUVSYPGUUKXRYNXTXSFEB
      UUONXMVEZMXMVEZWAVKUVOYPXTXSGEBUUKUVTUWAWAVJUVQUVAXTEUVTUVPUUTXSBUWAUVPUU
      CQXNUKRXOUKDXPUKCXQUKZGYPUKUUTUVOUWBYPGUUKAYNXQXPXOQXNFCDRUUOLXMVEZKXMVEZ
      JXMVEZIXMVEZWBVKUUCYPXQXPXOQXNGCDRUUKUWCUWDUWEUWFWBVJVKVKVJVKUVLUVJUFUVCU
      KZGUVCYDUOZUKZXLYFUVCVDUHZUWHVDUHUVLUWIUTUVNUVCYDUVNVBUVJUVCYPUWHVDVDUFGY
      MUVCYDWCWDWEXLUWIUWGGYEUKZYFXLUWHYEWPZUWIUWKUTXLYDYRWFUWLXLYDULUVHUMUNYRU
      LPUGWGOUVHULUMSWHWIXMYDYRWJVSUWGGUWHYEWKVSXLYEVDUHUWKYFUTXMYDUVMVBXLUWGYC
      GYEVDUWGYAFOUVCUJZUKZXLYCUWJUUNUFWLUWGUWNUTUVNUUNUFUUOWMYAUFFUVCYNUWMVDVD
      OYMUVCWNWOWEXLUWMYBWPZUWNYCUTXLOYRUHZUWOXLUVGUWPUVIOXFWQOYRXMWRVSYAFUWMYB
      WKVSWSWTXAXBWSXCXDXGXHUUDCDRBEUFHIJKLMNOQTUAUBUCUDUEXEXIVQYLFGUFOPSXJXK
      $.
      $( [11-Oct-2014] $)

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 5: Arithmetic sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t $.
    $( Lemma for arithmetic diophantine sets.  Convert polynomial-ness of an
       expression into a constraint suitable for ~ ralimi . $)
    rabdiophlem1 $p |- ( ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1
        ... N ) ) -> A. t e. ( NN0 ^m ( 1 ... N ) ) A e. ZZ ) $=
      ( cz c1 cfz co cmap cmpt cmzp cfv wcel wf wral cn0 mzpf eqid fmpt biimpri
      wss wi nn0ssz zex ovex mapss ssralv mp2b 3syl ) ADECFGZHGZBIZUIJKLUJDUKMZ
      BDLZAUJNZUMAOUIHGZNZUKUIPUNULAUJDBUKUKQRSODTUOUJTUNUPUAUBODUIUCECFUDUEUMA
      UOUJUFUGUH $.
      $( [10-Oct-2014] $)
  $}

  ${
    $d N a b c u t $.  $d M a b c u t $.  $d A a b c t $.
    rabdiophlem2.1 $e |- M = ( N + 1 ) $.
    $( Lemma for arithmetic diophantine sets.  Reuse a polynomial expression
       under a new quantifier. $)
    rabdiophlem2 $p |- ( ( N e. NN0 /\ ( u e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> ( t e. ( ZZ ^m ( 1 ... M ) ) |-> [_ ( t
        |` ( 1 ... N ) ) / u ]_ A ) e. ( mzPoly ` ( 1 ... M ) ) ) $=
      ( va vb cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv cv ax-17 wa cres csb vex
      wel hbcsb1 csbeq1a cbvmpt fveq1i wceq mapfzcons1cl adantlr wral mzpf eqid
      fmpt sylibr ad2antlr resex hbel eleq1d sylc csbeq1 fvmptg syl2anc syl5req
      wf rcla4 mpteq2dva cvv wss a1i caddc fzssp1 oveq2i syl6sseqr adantr simpr
      ovex mzpresrename syl3anc eqeltrd ) EIJZAKLEMNZONZCPZWDQRJZUAZBKLDMNZONZA
      BSZWDUBZCUCZPBWJWLWFRZPZWIQRZWHBWJWMWNWHWKWJJZUAZWNWLGWEAGSZCUCZPZRZWMWLW
      FXAAGHWECWTHSCJGTAHWSCGUDHGUEATUFAWSCUGUHUIWRWLWEJZWMKJZXBWMUJWCWQXCWGWKK
      DEFUKULZWRXCCKJZAWEUMZXDXEWGXGWCWQWGWEKWFVGXGWFWDUNAWEKCWFWFUOUPUQURXFXDA
      WLWEAGGWMKAGWLCWKWDBUDUSWSWLJATUFWSKJATUTASWLUJCWMKAWLCUGVAVHVBGWLWTWMWEK
      XAAWSWLCVCXAUOVDVEVFVIWHWIVJJZWDWIVKZWGWOWPJXHWHLDMVSVLWCXIWGWCWDLELVMNZM
      NWILEIVNDXJLMFVOVPVQWCWGVRBWFWDWIVTWAWB $.
      $( [10-Oct-2014] $)
  $}

  ${
    $d A a b c $.  $d N a b c t $.
    $( Diophantine set builder for nonnegativity constraints.  The first
       builder which uses a witness variable internally; an expression is
       nonnegative if there is a nonnegative integer equal to it. $)
    elnn0rabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN0
        } e. ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab cv wceq ax-17 wa
      csb wrex cdioph wb risset a1i rabbiia vex wel hbcsb1 hbeleq hbrex csbeq1a
      weq eqeq2d rexbidv cbvrab syl6eq caddc cres peano2nn0 adantr ovex nn0p1nn
      elfz1end sylib mzpproj sylancr eqid rabdiophlem2 eqrabdioph syl3anc eqeq1
      cvv cn csbeq1 rexrabdioph syldan eqeltrd ) CGHZAIJCKLZMLBNWBOPHZUAZBGHZAG
      WBMLZQZDRZAERZBUBZSZDGUCZEWFQZCUDPZWDWGWHBSZDGUCZAWFQZWMWGWQSWDWEWPAWFWEW
      PUEARWFHDBGUFUGUHUGWPWLAEDWFWHWFHZATWRETWPETWKADGWHGHATADWJADWIBEUIDEUJAT
      UKULUMAEUOZWOWKDGWSBWJWHAWIBUNUPUQURUSWAWCCJUTLZFRZPZAXAWBVAZBUBZSZFGJWTK
      LZMLQWTUDPHZWMWNHWDWTGHZFIXFMLZXBNXFOPZHZFXIXDNXJHXGWAXHWCCVBVCWDXFVOHWTX
      FHZXKJWTKVDWAXLWCWAWTVPHXLCVEWTVFVGVCFXFWTVHVIAFBWTCWTVJZVKFXBXDWTVLVMXEW
      KXBWJSDEFWTCXMWHXBWJVNWIXCSWJXDXBAWIXCBVQUPVRVSVT $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d ph y a b c $.  $d ps x a b c $.  $d ch x a b c $.  $d x y $.
    rexzrexnn0.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    rexzrexnn0.2 $e |- ( x = -u y -> ( ph <-> ch ) ) $.
    $( Rewrite a quantification over integers into a quantification over
       naturals. $)
    rexzrexnn0 $p |- ( E. x e. ZZ ph <-> E. y e. NN0 ( ps \/ ch ) ) $=
      ( cz wrex wo cn0 cv wcel wa cneg weq wb rcla4ev wceq rexlimiva cr simprbi
      elznn0 adantr simpr simplr equcom bicom 3imtr4i syl2anc ex zcn negneg syl
      cc eqcomd eqeq2d syl5ibrcom imp bicom1 3syl rcla4edv impancom orim12d mpd
      negeq r19.43 sylibr nn0z sylan nn0negz jaodan impbii ) ADHIZBCJZEKIZAVPDH
      DLZHMZANZBEKIZCEKIZJZVPVSVQKMZVQOZKMZJZWBVRWFAVRVQUAMWFVQUCUBUDVSWCVTWEWA
      VSWCVTVSWCNWCAVTVSWCUEVRAWCUFBAEVQKDEPABQEDPBAQFEDUGBAUHUIRUJUKVRWEAWAVRC
      AEWDKVRELZWDSZNVQWGOZSZACQCAQVRWHWJVRWJWHVQWDOZSVRWKVQVRVQUOMWKVQSVQULVQU
      MUNUPWHWIWKVQWGWDVFUQURUSGACUTVAVBVCVDVEBCEKVGVHTVOVNEKWGKMZBVNCWLWGHMBVN
      WGVIABDWGHFRVJWLWIHMCVNWGVKACDWIHGRVJVLTVM $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d N t $.  $d M t $.
    $( Diophantine set builder for the less or equals relation. $)
    lerabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A <_ B } e.
        ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab wral rabdiophlem1 3adant1
      w3a wa cle cmin cdioph wceq wb znn0sub ralimi r19.26 rabbi 3imtr3i syl2an
      wbr simp1 mzpsubmpt ancoms elnn0rabdioph syl2anc eqeltrd ) DEFZAGHDIJZKJZ
      BLUTMNZFZAVACLVBFZSZBCUAULZAEUTKJZOZCBUBJZEFZAVGOZDUCNZVCVDVHVKUDZUSVCBGF
      ZAVGPZCGFZAVGPZVMVDABDQACDQVNVPTZAVGPVFVJUEZAVGPVOVQTVMVRVSAVGBCUFUGVNVPA
      VGUHVFVJAVGUIUJUKRVEUSAVAVILVBFZVKVLFUSVCVDUMVCVDVTUSVDVCVTACBUTUNUORAVID
      UPUQUR $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for membership in a fixed set of upper
       integers. $)
    eluzrabdioph $p |- ( ( N e. NN0 /\ M e. ZZ /\ ( t e. ( ZZ ^m ( 1 ... N ) )
        |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) )
        | A e. ( ZZ>= ` M ) } e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv w3a cuz crab wa wb wral cdioph
      cle wbr wceq rabdiophlem1 eluz1 adantr bicomd adantl bitrd ex ralimdv imp
      ibar sylan2 rabbi sylib 3adant1 simp1 cvv ovex mzpconstmpt 3ad2ant2 simp3
      mpan lerabdioph syl3anc eqeltrd ) DEFZCGFZAGHDIJZKJZBLVKMNZFZOZBCPNFZAEVK
      KJZQZCBUBUCZAVQQZDUANZVJVNVRVTUDZVIVJVNRVPVSSZAVQTZWBVNVJBGFZAVQTZWDABDUE
      VJWFWDVJWEWCAVQVJWEWCVJWERVPWEVSRZVSVJVPWGSWECBUFUGWEWGVSSVJWEVSWGWEVSUNU
      HUIUJUKULUMUOVPVSAVQUPUQURVOVIAVLCLVMFZVNVTWAFVIVJVNUSVJVIWHVNVKUTFVJWHHD
      IVAACVKVBVEVCVIVJVNVDACBDVFVGVH $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for positivity. $)
    elnnrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN }
        e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv wa cn crab cuz cdioph wb cv 1z
      elnnuz a1i rabbiia eluzrabdioph mp3an2 syl5eqel ) CDEZAFGCHIZJIBKUILMEZNB
      OEZADUIJIZPBGQMEZAULPZCRMZUKUMAULUKUMSATULEBUBUCUDUHGFEUJUNUOEUAABGCUEUFU
      G $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for the strict less than relation. $)
    ltrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A < B } e.
        ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab wral rabdiophlem1 3adant1
      w3a wa clt wbr cmin cn cdioph wceq wb znnsub ralimi r19.26 3imtr3i syl2an
      rabbi simp1 mzpsubmpt ancoms elnnrabdioph syl2anc eqeltrd ) DEFZAGHDIJZKJ
      ZBLVAMNZFZAVBCLVCFZSZBCUAUBZAEVAKJZOZCBUCJZUDFZAVHOZDUENZVDVEVIVLUFZUTVDB
      GFZAVHPZCGFZAVHPZVNVEABDQACDQVOVQTZAVHPVGVKUGZAVHPVPVRTVNVSVTAVHBCUHUIVOV
      QAVHUJVGVKAVHUMUKULRVFUTAVBVJLVCFZVLVMFUTVDVEUNVDVEWAUTVEVDWAACBVAUOUPRAV
      JDUQURUS $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for inequality.  This not quite trivial theorem
       touches on something important; Diophantine sets are not closed under
       negation, but they contain an important subclass that is, namely the
       recursive sets.  With this theorem and De Morgan's laws, all
       quantifier-free formulae can be negated. $)
    nerabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A =/= B }
        e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz co cmap cmpt cfv crab clt wbr rabdiophlem1 wa cr zre syl2an
      wral c1 cfz cmzp w3a wo cdioph wceq wb lttri2 ralimi r19.26 rabbi 3imtr3i
      wne 3adant1 ltrabdioph 3com23 orrabdioph syl2anc eqeltrd ) DEFZAGUADUBHZI
      HZBJVBUCKZFZAVCCJVDFZUDZBCUNZAEVBIHZLZBCMNZCBMNZUEZAVILZDUFKZVEVFVJVNUGZV
      AVEBGFZAVITZCGFZAVITZVPVFABDOACDOVQVSPZAVITVHVMUHZAVITVRVTPVPWAWBAVIVQBQF
      CQFWBVSBRCRBCUISUJVQVSAVIUKVHVMAVIULUMSUOVGVKAVILVOFVLAVILVOFZVNVOFABCDUP
      VAVFVEWCACBDUPUQVKVLADURUSUT $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d N a b c d t $.  $d A a b c d $.  $d B a b c d $.

    $( Divisibility is a Diophantine relation. $)
    dvdsrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A || B } e.
        ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cz c1 co cmap cmpt cfv crab cmul wceq wo ax-17 cfz cv
      cmzp w3a cdivides wbr cneg wrex cdioph wral rabdiophlem1 wa divides oveq1
      weq eqeq1d rexzrexnn0 syl6bb ralimi r19.26 3imtr3i syl2an 3adant1 csb wel
      wb rabbi vex hbcsb1 hbov hbeq hbor csbeq1a oveq2d eqeq12d orbi12d rexbidv
      hbrex cbvrab caddc cres simp1 peano2nn0 3ad2ant1 ovex cn nn0p1nn elfz1end
      cvv mzpproj sylancr adantr rabdiophlem2 mzpmulmpt syl2anc 3adant3 3adant2
      sylib eqid eqrabdioph syl3anc mzpnegmpt syl orrabdioph oveq1d rexrabdioph
      negeq csbeq1 syl5eqel eqeltrd ) DHIZAJKDUALZMLZBNXLUCOZIZAXMCNXNIZUDZBCUE
      UFZAHXLMLZPZEUBZBQLZCRZYAUGZBQLZCRZSZEHUHZAXSPZDUIOZXOXPXTYIRZXKXOBJIZAXS
      UJZCJIZAXSUJZYKXPABDUKACDUKYLYNULZAXSUJXRYHVFZAXSUJYMYOULYKYPYQAXSYPXRFUB
      ZBQLZCRZFJUHYHFBCUMYTYCYFFEFEUOYSYBCYRYABQUNUPYRYDRYSYECYRYDBQUNUPUQURUSY
      LYNAXSUTXRYHAXSVGVAVBVCXQYIYAAYRBVDZQLZAYRCVDZRZYDUUAQLZUUCRZSZEHUHZFXSPZ
      YJYHUUHAFGXSGUBZXSIZATUUKFTYHFTUUGAEHYAHIATUUDUUFAAGGUUBUUCAGYAUUAQGEVEAT
      UUJQIATZAGYRBFVHZGFVEATZVIZVJAGYRCUUMUUNVIZVKAGGUUEUUCAGYDUUAQUUJYDIATUUL
      UUOVJUUPVKVLVRAFUOZYGUUGEHUUQYCUUDYFUUFUUQYBUUBCUUCUUQBUUAYAQAYRBVMZVNAYR
      CVMZVOUUQYEUUECUUCUUQBUUAYDQUURVNUUSVOVPVQVSXQXKDKVTLZUUJOZAUUJXLWAZBVDZQ
      LZAUVBCVDZRZUVAUGZUVCQLZUVERZSZGHKUUTUALZMLZPUUTUIOZIZUUIYJIXKXOXPWBXQUVF
      GUVLPUVMIZUVIGUVLPUVMIZUVNXQUUTHIZGJUVKMLZUVDNUVKUCOZIZGUVRUVENUVSIZUVOXK
      XOUVQXPDWCWDZXKXOUVTXPXKXOULZGUVRUVANUVSIZGUVRUVCNUVSIZUVTXKUWDXOXKUVKWII
      UUTUVKIZUWDKUUTUAWEXKUUTWFIUWFDWGUUTWHWRGUVKUUTWJWKWLZAGBUUTDUUTWSZWMZGUV
      AUVCUVKWNWOWPXKXPUWAXOAGCUUTDUWHWMWQZGUVDUVEUUTWTXAXQUVQGUVRUVHNUVSIZUWAU
      VPUWBXKXOUWKXPUWCGUVRUVGNUVSIZUWEUWKUWCUWDUWLUWGGUVAUVKXBXCUWIGUVGUVCUVKW
      NWOWPUWJGUVHUVEUUTWTXAUVFUVIGUUTXDWOUVJUUGUVAUUAQLZUUCRZUVGUUAQLZUUCRZSEF
      GUUTDUWHYAUVARZUUDUWNUUFUWPUWQUUBUWMUUCYAUVAUUAQUNUPUWQUUEUWOUUCUWQYDUVGU
      UAQYAUVAXGXEUPVPYRUVBRZUWNUVFUWPUVIUWRUWMUVDUUCUVEUWRUUAUVCUVAQAYRUVBBXHZ
      VNAYRUVBCXHZVOUWRUWOUVHUUCUVEUWRUUAUVCUVGQUWSVNUWTVOVPXFWOXIXJ $.
      $( [11-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 6 miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d G a $.  $d F a $.  $d X a $.  $d A a $.
    $( Function value of a composition.  Like ~ fvco2 but with no restrictions
       on ` F ` .  Possibly a replacement for ~ fvco2 ? $)
    fvco4 $p |- ( ( G Fn A /\ X e. A ) -> ( ( F o. G ) ` X ) =
        ( F ` ( G ` X ) ) ) $=
      ( va wfn wcel wa ccom csn cima cv wceq cab cuni imaco fnsnfv eqcomd df-fv
      cfv imaeq2d syl5eq eqeq1d abbidv unieqd 3eqtr4g ) CAFDAGHZBCIZDJZKZELJZMZ
      ENZOBDCTZJZKZUKMZENZODUHTUNBTUGUMURUGULUQEUGUJUPUKUGUJBCUIKZKUPBCUIPUGUSU
      OBUGUOUSADCQRUAUBUCUDUEEDUHSEUNBSUF $.
      $( [16-Oct-2014] $)
  $}

  ${
    $d A a $.

    $( A finite set of positive integers is a set of positive integers. $)
    fz1ssnn $p |- ( 1 ... A ) C_ NN $=
      ( va c1 cfz co cn cv elfznn ssriv ) BCADEFBGAHI $.
      $( [16-Oct-2014] $)
  $}

  ${
    ftp.a $e |- A e. _V $.
    ftp.b $e |- B e. _V $.
    ftp.c $e |- C e. _V $.
    ftp.d $e |- X e. _V $.
    ftp.e $e |- Y e. _V $.
    ftp.f $e |- Z e. _V $.
    ftp.g $e |- A =/= B $.
    ftp.h $e |- A =/= C $.
    ftp.i $e |- B =/= C $.
    $( A function with a domain of three elements. $)
    ftp $p |- { <. A , X >. , <. B , Y >. , <. C , Z >. } : { A , B , C } -->
        { X , Y , Z } $=
      ( ctp cop wf cpr wceq csn cun wa cin wne fpr ax-mp eqid1 fsn mpbir pm3.2i
      c0 wcel wn wo necomi df-ne mpbi pm3.2ni elpr mtbir disjsn fun mp2an df-tp
      feq1i feq23i bitri ) ABCPZDEFPZADQZBEQZCFQZPZRZABSZCUAZUBZDESZFUAZUBZVKVL
      SZVMUAZUBZRZVPVSWBRZVQVTWCRZUCVPVQUDULTZWEWFWGABUEWFMABDEGHJKUFUGWGWCWCTW
      CUHCFWCILUIUJUKWHCVPUMZUNWICATZCBTZUOWJWKCAUEWJUNACNUPCAUQURCBUEWKUNBCOUP
      CBUQURUSCABIUTVAVPCVBUJVPVQVSVTWBWCVCVDVOVIVJWDRWEVIVJVNWDVKVLVMVEVFVIVJV
      RWAWDABCVEDEFVEVGVHUJ $.
      $( [17-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Diophantine sets 6: reusability.  renumbering of variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d W a b c p u t w $.  $d S a b c p u t w $.  $d N a b c p u t w $.
    $d P a b c p u t w $.
    eldioph4b.a $e |- W e. _V $.
    eldioph4b.b $e |- -. W e. Fin $.
    eldioph4b.c $e |- ( W i^i NN ) = (/) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    eldioph4b $p |- ( S e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. p e. ( mzPoly ` (
        W u. ( 1 ... N ) ) ) S = { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0
        ^m W ) ( p ` ( t u. w ) ) = 0 } ) ) $=
      ( vu cfv wcel cn0 cun cc0 wceq wrex cres wa c0 cdioph cv cmap co cfz crab
      c1 cmzp eldiophelnn0 cab cvv cfn wn wb ovex unex jctr intnanr unfir ssun2
      wss pm3.2i eldioph2b sylancl elmapssres mp3an23 adantr ssun1 uncom eqtr4i
      mto resundi wfn nn0ex elmap biimpi ffn fnresdm 3syl syl5eq fveq2d biimpar
      eqeq1d uneq2 rcla4ev syl2anc jca eleq1 rexbidv anbi12d syl5ibrcom expimpd
      wf uneq1 ancomsd rexlimiv cin cn elfznn ssriv sslin ax-mp sseqtri reseq2i
      ss0 res0 eqtri elmapresaun mp3an3 ancoms syl5eqel elmapresaunres2 syl5req
      reseq1 simpr eqeq2d syl12anc ex rexlimdva imp impbii df-rab eqeq2i rexbii
      fveq2 abbii syl6bb biadan2 ) CDUAKLZDMLZCBUBZAUBZNZFUBZKZOPZAMEUCUDZQZBMU
      GDUEUDZUCUDZUFZPZFEYSNZUHKZQZCDUIYJYICYKJUBZYSRZPZUUFYNKZOPZSZJMUUCUCUDZQ
      ZBUJZPZFUUDQZUUEYJYJUUCUKLZSUUCULLZUMZYSUUCVAZSYIUUPUNYJUUQEYSGUGDUEUOZUP
      ZUQUUSUUTUUREULLZYSULLZSUVCUVDHUREYSUSVKYSEUTZVBJBCUUCDFVCVDUUOUUBFUUDUUN
      UUACUUNYKYTLZYRSZBUJUUAUUMUVGBUUMUVGUUKUVGJUULUUFUULLZUUJUUHUVGUVHUUJUUHU
      VGUVHUUJSZUVGUUHUUGYTLZUUGYLNZYNKZOPZAYQQZSUVIUVJUVNUVHUVJUUJUVHUUTUUQUVJ
      UVEUVBUUFMUUCYSVEVFVGUVIUUFERZYQLZUUGUVONZYNKZOPZUVNUVHUVPUUJUVHEUUCVAUUQ
      UVPEYSVHUVBUUFMUUCEVEVFVGUVHUVSUUJUVHUVRUUIOUVHUVQUUFYNUVHUVQUUFUUCRZUUFU
      VQUVOUUGNUVTUUGUVOVIUUFEYSVLVJUVHUUCMUUFWMZUUFUUCVMUVTUUFPUVHUWAMUUCUUFVN
      UVBVOVPUUCMUUFVQUUCUUFVRVSVTWAWCWBUVMUVSAUVOYQYLUVOPZUVLUVROUWBUVKUVQYNYL
      UVOUUGWDWAWCWEWFWGUUHUVFUVJYRUVNYKUUGYTWHUUHYPUVMAYQUUHYOUVLOUUHYMUVKYNYK
      UUGYLWNWAWCWIWJWKWLWOWPUVFYRUUMUVFYPUUMAYQUVFYLYQLZSZYPUUMUWDYPSYMUULLZYK
      YMYSRZPZYPUUMUWDUWEYPUWDYMYLYKNZUULYKYLVIZUWCUVFUWHUULLZUWCUVFYLEYSWQZRZY
      KUWKRZPZUWJUWLTUWMUWLYLTRTUWKTYLUWKTVAUWKTPUWKEWRWQZTYSWRVAUWKUWOVAJYSWRU
      UFDWSWTYSWREXAXBIXCUWKXEXBZXDYLXFXGUWMYKTRTUWKTYKUWPXDYKXFXGVJZEYSMYLYKGU
      VAXHXIXJXKVGUWDUWGYPUWDUWFUWHYSRZYKYMUWHPUWFUWRPUWIYMUWHYSXNXBUWCUVFUWRYK
      PZUWCUVFUWNUWSUWQEYSMYLYKGUVAXLXIXJXMVGUWDYPXOUUKUWGYPSJYMUULUUFYMPZUUHUW
      GUUJYPUWTUUGUWFYKUUFYMYSXNXPUWTUUIYOOUUFYMYNYEWCWJWEXQXRXSXTYAYFYRBYTYBVJ
      YCYDYGYH $.

    $( [16-Oct-2014] $)
    eldioph4i $p |- ( ( N e. NN0 /\ P e. ( mzPoly ` ( W u. ( 1 ... N ) ) ) ) ->
        { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0 ^m W ) ( P ` ( t u. w ) )
        = 0 } e. ( Dioph ` N ) ) $=
      ( va vb vp cn0 wcel co cun cfv cv cc0 wceq wrex cfz cmzp cmap crab cdioph
      c1 wa weq uneq1 fveq2d eqeq1d rexbidv uneq2 cbvrexv cbvrabv fveq1 rabbidv
      syl6bb eqeq2d rcla4ev mpan2 anim2i eldioph4b sylibr ) DLMZCEUFDUANZOUBPZM
      ZUGVEBQZAQZOZCPZRSZALEUCNZTZBLVFUCNZUDZIQZJQZOZKQZPZRSZJVNTZIVPUDZSZKVGTZ
      UGVQDUEPMVHWGVEVHVQVTCPZRSZJVNTZIVPUDZSZWGVOWJBIVPBIUHZVOVRVJOZCPZRSZAVNT
      WJWMVMWPAVNWMVLWORWMVKWNCVIVRVJUIUJUKULWPWIAJVNAJUHZWOWHRWQWNVTCVJVSVRUMU
      JUKUNURUOWFWLKCVGWACSZWEWKVQWRWDWJIVPWRWCWIJVNWRWBWHRVTWACUPUKULUQUSUTVAV
      BJIVQDEKFGHVCVD $.
      $( [16-Oct-2014] $)
  $}

  ${
    $d S a b c d e f g h i $.  $d M a b c d e f g h i $.
    $d N a b c d e f g h i $.  $d F a b c d e f g h i $.
    $( Change variables in a Diophantine set, using class notation.  This
       allows already proved Diophantine sets to be reused in contexts with
       more variables. $)
    diophren $p |- ( ( S e. ( Dioph ` N ) /\ M e. NN0 /\
          F : ( 1 ... N ) --> ( 1 ... M ) ) ->
        { a e. ( NN0 ^m ( 1 ... M ) ) | ( a o. F ) e. S } e. ( Dioph ` M ) ) $=
      ( vd cfv wcel cn0 c1 co ccom cmap wa cun cc0 wceq cz cn c0 vc vb ve wf cv
      cdioph cfz crab cdif wrex cmzp cvv zex difexg ax-mp cfn com ominf cen wbr
      wb omex caddc nnuz ax-1cn addid2i fveq2i eqtr4i difeq2i 0z lzenom eqbrtri
      cuz enfi mp2an mtbir incom disjdif eqtri eldioph4b cres cmpt simpr simplr
      cin ad2antrr nn0ex ovex mapco2 syl2anc uneq1 fveq2d eqeq1d rexbidv elrab3
      cid syl ad3antrrr w3a coundi coundir elmap biimpi 3ad2ant3 fz1ssnn ssdisj
      simp1 wss a1i coeq0i syl3anc uneq2d syl5eq syl6eq 3ad2ant2 wf1o f1oi f1of
      un0 mp3an23 wfun wrel elmapfun coires1 3syl wfn ffn fnresdm eqtrd uneq12d
      funrel uncom syl5req nn0ssz unex mapss reseq2i res0 elmapresaun oveq2i
      syl6eleq mp3an3 sseldi adantll coeq1 fvmpt eqtr4d rexbidva bitrd rabbidva
      eqid fvex simplll simpllr id1 fun feq1i sylib mzprename eldioph4i eqeltrd
      syl21anc eleq2 rabbidv eleq1d syl5ibrcom rexlimdva expimpd syl5bi impcom
      3impb ) ADUFGHZCIHZJDUGKZJCUGKZBUDZEUEZBLZAHZEIUVOMKZUHZCUFGZHZUVMUVPNZUV
      LUWCUVLDIHZAUAUEZFUEZOZUBUEZGZPQZFIRSUIZMKZUJZUAIUVNMKZUHZQZUBUWLUVNOZUKG
      ZUJZNUWDUWCFUAADUWLUBRULHUWLULHUMRSULUNUOZUWLUPHZUQUPHZURUQULHUWLUQUSUTUX
      BUXCVAVBUWLRPJVCKZVMGZUIZUQUSSUXERSJVMGUXEVDUXDJVMJVEVFVGVHVIPRHUXFUQUSUT
      VJPVKUOVLUWLUQULVNVOVPZUWLSWESUWLWEZTUWLSVQSRVRZVSZVTUWDUWEUWTUWCUWDUWENZ
      UWQUWCUBUWSUXKUWIUWSHZNZUWCUWQUVRUWPHZEUVTUHZUWBHUXMUXOUVQUWGOZUCRUWLUVOO
      ZMKZUCUEZBWPUWLWAZOZLZUWIGZWBZGZPQZFUWMUJZEUVTUHZUWBUXMUXNUYGEUVTUXMUVQUV
      THZNZUXNUVRUWGOZUWIGZPQZFUWMUJZUYGUYJUVRUWOHZUXNUYNVAUYJUYIUVPUYOUXMUYIWC
      UXKUVPUXLUYIUVMUVPUWEWDZWFUVQIUVOBUVNWGJCUGWHZJDUGWHWIWJUWNUYNUAUVRUWOUWF
      UVRQZUWKUYMFUWMUYRUWJUYLPUYRUWHUYKUWIUWFUVRUWGWKWLWMWNWOWQUYJUYMUYFFUWMUY
      JUWGUWMHZNZUYLUYEPUYTUYLUXPUYALZUWIGZUYEUYTUYKVUAUWIUYTUVPUYIUYSUYKVUAQUX
      KUVPUXLUYIUYSUYPWRUXMUYIUYSWDUYJUYSWCUVPUYIUYSWSZVUAUXPBLZUXPUXTLZOUYKUXP
      BUXTWTVUCVUDUVRVUEUWGVUCVUDUVRTOZUVRVUCVUDUVRUWGBLZOVUFUVQUWGBXAVUCVUGTUV
      RVUCUWLIUWGUDZUVPUWLUVOWEZTQZVUGTQUYSUVPVUHUYIUYSVUHIUWLUWGWGUXAXBXCZXDUV
      PUYIUYSXGVUJVUCVUIUVOUWLWEZTUWLUVOVQUVOSXHUXHTQZVULTQZCXEUXIUVOSUWLXFVOZV
      SXIUWGBUWLIUVNUVOXJXKXLXMUVRXSXNVUCVUETUWGOZUWGVUCVUEUVQUXTLZUWGUXTLZOVUP
      UVQUWGUXTXAVUCVUQTVURUWGVUCUVOIUVQUDZVUQTQZUYIUVPVUSUYSUYIVUSIUVOUVQWGUYQ
      XBXCXOVUSUWLUWLUXTUDZVUNVUTUWLUWLUXTXPVVAUWLXQUWLUWLUXTXRUOZVUOUVQUXTUVOI
      UWLUWLXJXTWQUYSUVPVURUWGQUYIUYSVURUWGUWLWAZUWGUYSUWGYAUWGYBVURVVCQUWGIUWL
      YCUWGYKUWGUWLYDYEUYSVUHUWGUWLYFVVCUWGQVUKUWLIUWGYGUWLUWGYHYEYIXDYJXMVUPUW
      GTOUWGTUWGYLUWGXSVSXNYJYMXKWLUYTUXPUXRHZUYEVUBQUYIUYSVVDUXMUYIUYSNIUXQMKZ
      UXRUXPIRXHVVEUXRXHYNIRUXQUMUWLUVOUXAUYQYOZYPUOUYIUYSUVQVULWAZUWGVULWAZQZU
      XPVVEHVVGTVVHVVGUVQTWATVULTUVQVUOYQUVQYRVSVVHUWGTWATVULTUWGVUOYQUWGYRVSVH
      UYIUYSVVIWSUXPIUVOUWLOZMKVVEUVOUWLIUVQUWGUYQUXAYSVVJUXQIMUVOUWLYLYTUUAUUB
      UUCUUDUCUXPUYCVUBUXRUYDUXSUXPQUYBVUAUWIUXSUXPUYAUUEWLUYDUUKVUAUWIUULUUFWQ
      UUGWMUUHUUIUUJUXMUVMUYDUXQUKGHZUYHUWBHUVMUVPUWEUXLUUMUXMUXQULHZUXLUWRUXQU
      YAUDZVVKVVLUXMVVFXIUXKUXLWCUXMUVPVVMUVMUVPUWEUXLUUNUVPUWRUXQUXTBOZUDZVVMU
      VPVVAUVPUWLUVNWEZTQZVVOVVAUVPVVBXIUVPUUOVVQUVPVVPUVNUWLWEZTUWLUVNVQUVNSXH
      VUMVVRTQDXEUXIUVNSUWLXFVOVSXIUWLUVNUWLUVOUXTBUUPUVBUWRUXQVVNUYAUXTBYLUUQU
      URWQUCUYAUWIUWRUXQUUSXKFEUYDCUWLUXAUXGUXJUUTWJUVAUWQUWAUXOUWBUWQUVSUXNEUV
      TAUWPUVRUVCUVDUVEUVFUVGUVHUVIUVJUVK $.
      $( [16-Oct-2014] $)
  $}

  ${
    $d ph b $.  $d A a b $.  $d B a b $.  $d F a b $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    rabrenfdioph $p |- ( ( B e. NN0 /\ F : ( 1 ... A ) --> ( 1 ... B ) /\
          { a e. ( NN0 ^m ( 1 ... A ) ) | ph } e. ( Dioph ` A ) ) ->
        { b e. ( NN0 ^m ( 1 ... B ) ) | [ ( b o. F ) / a ] ph } e.
          ( Dioph ` B ) ) $=
      ( cn0 wcel c1 cfz co wf cmap crab cdioph cfv w3a cv wa ovex simplr mapco2
      ccom wsbc wceq simpr nn0ex syl2anc ax-17 elrabsf syl6bbr rabbidva 3adant3
      biantrurd diophren 3coml eqeltrd ) CGHZIBJKZICJKZDLZAEGUSMKZNZBOPHZQAEFRZ
      DUCZUDZFGUTMKZNZVFVCHZFVHNZCOPZURVAVIVKUEVDURVASZVGVJFVHVMVEVHHZSZVGVFVBH
      ZVGSVJVOVPVGVOVNVAVPVMVNUFURVAVNUAVEGUTDUSUGICJTIBJTUBUHUNAEFVFVBVEVBHEUI
      UJUKULUMVDURVAVKVLHVCDCBFUOUPUQ $.
      $( [17-Oct-2014] $)
  $}


  ${
    $d ps a $.  $d ph b $.  $d X a b $.  $d Y a b $.  $d Z a b $.  $d N a b $.
    rabren3dioph.a $e |- ( ( ( a ` 1 ) = ( b ` X ) /\ ( a ` 2 ) = ( b ` Y ) /\
      ( a ` 3 ) = ( b ` Z ) ) -> ( ph <-> ps ) ) $.
    rabren3dioph.b $e |- X e. ( 1 ... N ) $.
    rabren3dioph.c $e |- Y e. ( 1 ... N ) $.
    rabren3dioph.d $e |- Z e. ( 1 ... N ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    rabren3dioph $p |- ( ( N e. NN0 /\ { a e. ( NN0 ^m ( 1 ... 3 ) ) | ph } e.
        ( Dioph ` 3 ) ) -> { b e. ( NN0 ^m ( 1 ... N ) ) | ps } e.
        ( Dioph ` N ) ) $=
      ( wcel c1 c3 co cfv c2 wceq mp2an cn0 cfz cmap crab cdioph wa cv cop ccom
      ctp wsbc wb vex tpex coex w3a wfn wne 1ne2 1re 3re 1lt3 ltneii necomi 2re
      2lt3 cn 1nn elexi 2nn 3nn fntp mp3an tpid1 fvco4 fvtp1 fveq2i eqtri tpid2
      fvtp2 tpid3 fvtp3 3pm3.2i fveq1 eqeq1d 3anbi123d mpbiri syl sbcie rabbiia
      a1i wf wss ftp caddc cz fztp ax-mp ax-1cn 2cn addcomi eqtr4i oveq2i eqidd
      1z df-3 1p1e2apr1 tpeq123d 3eqtr3i feq2i mpbir tpss mpbi fss rabrenfdioph
      mp3an2 syl5eqelr ) CUAMZAGUANOUBPZUCPUDOUEQMZUFBHUANCUBPZUCPZUDAGHUGZNDUH
      ZREUHZOFUHZUJZUIZUKZHYBUDZCUEQZYIBHYBYIBULYCYBMABGYHYCYGHUMYDYEYFUNUOGUGZ
      YHSZNYLQZDYCQZSZRYLQZEYCQZSZOYLQZFYCQZSZUPZABULYMUUCNYHQZYOSZRYHQZYRSZOYH
      QZUUASZUPUUEUUGUUIUUDNYGQZYCQZYOYGNROUJZUQZNUULMUUDUUKSNRURZNOURZROURZUUM
      USONNOUTVAVBVCVDZORROVEVAVFVCVDZNRODEFNVGVHVIZRVGVJVIZOVGVKVIZVLVMZNROUUS
      VNUULYCYGNVOTUUJDYCUUNUUOUUJDSUSUUQNRODEFUUSDYAJVIZVPTVQVRUUFRYGQZYCQZYRU
      UMRUULMUUFUVESUVBNROUUTVSUULYCYGRVOTUVDEYCUUNUUPUVDESUSUURNRODEFUUTEYAKVI
      ZVTTVQVRUUHOYGQZYCQZUUAUUMOUULMUUHUVHSUVBNROUVAWAUULYCYGOVOTUVGFYCUUOUUPU
      VGFSUUQUURNRODEFUVAFYALVIZWBTVQVRWCYMYPUUEYSUUGUUBUUIYMYNUUDYONYLYHWDWEYM
      YQUUFYRRYLYHWDWEYMYTUUHUUAOYLYHWDWEWFWGIWHWIWKWJXRXSYAYGWLZXTYJYKMXSDEFUJ
      ZYGWLZUVKYAWMZUVJUVLUULUVKYGWLNRODEFUUSUUTUVAUVCUVFUVIUSUUQUURWNXSUULUVKY
      GNNRWOPZUBPZNNNWOPZUVNUJZXSUULNWPMZUVOUVQSXENWQWRUVNONUBUVNRNWOPONRWSWTXA
      XFXBZXCUVRUVQUULSXEUVRNNUVPRUVNOUVRNXDUVPRSUVRXGWKUVNOSUVRUVSWKXHWRXIXJXK
      DYAMZEYAMZFYAMZUPUVMUVTUWAUWBJKLWCDEFYAUVCUVFUVIXLXMXSUVKYAYGXNTAOCYGGHXO
      XPXQ $.
      $( [17-Oct-2014] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Pigeonhole Principle and cardinality helpers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( these were proved before I understood explicit substitution and could be much simplified with it; this along with AC removal makes them a high priority to reprove $)

  ${
    $d A x y a b c d $.  $d B x y a b c d $.  $d C y a b c d $.
    $d D x a b c d $.  $d ph x y a b c d $.
    fphpd.a $e |- ( ph -> B ~< A ) $.
    fphpd.b $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    fphpd.c $e |- ( x = y -> C = D ) $.
    $( Pigeonhole principle expressed with implicit substitution.  If the range
       is smaller than the domain, two inputs must be mapped to the same
       output. $)
    fphpd $p |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ C = D ) ) $=
      ( va vb wceq weq wi wral wn wa wcel ax-17 cv wne wrex cdom wbr csdm con2i
      domnsym syl cvv sdomex simprd adantr csb vex wel hbcsb1 hbel eleq1 anbi2d
      id csbeq1a eleq1d imbi12d chvar ex wb csbid csbief eqeq12i imbi1i 2ralbii
      hbim hbeq csbeq1 eqeq1d eqeq1 eqeq2d eqeq2 rcla42 com12 sylbir syl6 dom2d
      impbid1 adantl sylc mtand ancom df-ne anbi1i pm4.61 3bitr4i rexbii rexnal
      bitri sylibr ) AFGMZBCNZOZCDPZBDPZQZBUAZCUAZUBZWRRZCDUCZBDUCZAXBDEUDUEZAE
      DUFUEZXJQHXJXKDEUHUGUIAXBRZXLDUJSZXJXLVAAXMXBAXKXMHXKEUJSXMEDUKULUIUMXLKL
      DEBKUAZFUNZBLUAZFUNZUJAXNDSZXOESZOXBAXRXSAXDDSZRZFESZOAXRRZXSOBKYCXSBYCBT
      BLLXOEBLXNFKUOLKUPBTUQZXPESBTURVMBKNZYAYCYBXSYEXTXRAXDXNDUSUTYEFXOEBXNFVB
      VCVDIVEVFUMXBXRXPDSRZXOXQMZKLNZVGZOAXBYFYGYHOZYIXBBXDFUNZBXEFUNZMZWSOZCDP
      BDPZYFYJOYNWTBCDDYMWRWSYKFYLGBFVHBKXEFGCUOZXNGSBTJVIVJVKVLYFYOYJYNYJXOYLM
      ZKCNZOBCXNXPDDYQYRBBLLXOYLYDBLXEFYPLCUPBTUQVNYRBTVMYJCTYEYMYQWSYRYEYKXOYL
      BXDXNFVOVPXDXNXEVQVDCLNZYQYGYRYHYSYLXQXOBXEXPFVOVRXEXPXNVSVDVTWAWBYJYGYHY
      JVABXNXPFVOWEWCWFWDWGWHXIXAQZBDUCXCXHYTBDXHWTQZCDUCYTXGUUACDWSQZWRRWRUUBR
      XGUUAUUBWRWIXFUUBWRXDXEWJWKWRWSWLWMWNWTCDWOWPWNXABDWOWPWQ $.
      $( [19-Oct-2014] $)
  $}

  ${
    $d ph x y z a b c $.  $d A x y z a b c $.  $d B z a b c $.
    $d C x y a b c $.  $d D y z a b c $.  $d E x z a b c $.
    fphpdo.1 $e |- ( ph -> A C_ RR ) $.
    fphpdo.2 $e |- ( ph -> B e. _V ) $.
    fphpdo.3 $e |- ( ph -> B ~< A ) $.
    fphpdo.4 $e |- ( ( ph /\ z e. A ) -> C e. B ) $.
    fphpdo.5 $e |- ( z = x -> C = D ) $.
    fphpdo.6 $e |- ( z = y -> C = E ) $.
    $( Pigeonhole principle for sets of real numbers with implicit output
       reordering. $)
    fphpdo $p |- ( ph -> E. x e. A E. y e. A ( x < y /\ D = E ) ) $=
      ( vb wceq wa clt wcel vc cv wne cmpt cfv wrex wf eqid fmptd ffvelrn sylan
      wbr fveq2 fphpd wo cr sselda adantrr adantr adantrl lttri2 syl2anc simprl
      wb ad2antrr simprr simpr simplr weq breq1 eqeq1d anbi12d eqeq2d syl112anc
      breq2 rcla42ev ex eqcomd jaod anbi2d eleq1d imbi12d chvarv fvmptg adantlr
      wi eleq1 eqeq12d biimpd anim2d reximdva sylbid expimpd ancomsd rexlimdvva
      syld mpd ) APUBZUAUBZUCZWRDEGUDZUEZWSXAUEZQZRZUAEUFPEUFBUBZCUBZSULZHIQZRZ
      CEUFZBEUFZAPUAEFXBXCLAEFXAUGWRETZXBFTADEGFXAMXAUHZUIEFWRXAUJUKWRWSXAUMUNA
      XEXLPUAEEAXMWSETZRZRZXDWTXLXQXDWTXLXQXDRZWTWRWSSULZWSWRSULZUOZXLXRWRUPTZW
      SUPTZWTYAVDXQYBXDAXMYBXOAEUPWRJUQURUSXQYCXDAXOYCXMAEUPWSJUQUTUSWRWSVAVBXR
      YAXHXFXAUEZXGXAUEZQZRZCEUFZBEUFZXLXRXSYIXTXRXSYIXRXSRXMXOXSXDYIXQXMXDXSAX
      MXOVCZVEXQXOXDXSAXMXOVFZVEXRXSVGXQXDXSVHYGXSXDRWRXGSULZXBYEQZRBCWRWSEEBPV
      IZXHYLYFYMXFWRXGSVJYNYDXBYEXFWRXAUMVKVLCUAVIZYLXSYMXDXGWSWRSVOYOYEXCXBXGW
      SXAUMVMVLVPVNVQXRXTYIXRXTRZXOXMXTXCXBQZYIXQXOXDXTYKVEXQXMXDXTYJVEXRXTVGYP
      XBXCXQXDXTVHVRYGXTYQRWSXGSULZXCYEQZRBCWSWREEBUAVIZXHYRYFYSXFWSXGSVJYTYDXC
      YEXFWSXAUMVKVLCPVIZYRXTYSYQXGWRWSSVOUUAYEXBXCXGWRXAUMVMVLVPVNVQVSXQYIXLWF
      ZXDAUUBXPAYHXKBEAXFETZRZYGXJCEUUDXGETZRZYFXIXHUUFYFXIUUFYDHYEIUUFUUCHFTZY
      DHQAUUCUUEVHUUDUUGUUEADUBZETZRZGFTZWFZUUDUUGWFDBDBVIZUUJUUDUUKUUGUUMUUIUU
      CAUUHXFEWGVTUUMGHFNWAWBMWCUSDXFGHEFXANXNWDVBUUFUUEIFTZYEIQUUDUUEVGAUUEUUN
      UUCUULAUUERZUUNWFDCDCVIZUUJUUOUUKUUNUUPUUIUUEAUUHXGEWGVTUUPGIFOWAWBMWCWED
      XGGIEFXAOXNWDVBWHWIWJWKWKUSUSWPWLWMWNWOWQ $.
      $( [12-Sep-2014] $)
  $}

  $( An infinite subset of a countable set is countable, without using
     choice. $)
  ctbnfien $p |- ( ( ( X ~~ om /\ Y ~~ om ) /\
        ( A C_ X /\ -. A e. Fin ) ) -> A ~~ Y ) $=
    ( com cen wbr wa wss cfn wcel wn csdm isfinite3 notbii wo cdom cvv wi relen
    syl2anc brrelexi ssdom2g syl simpl domentr brdom2 sylib adantlr syl5bi impr
    imp ord omex ensym ad2antlr entr ) BDEFZCDEFZGZABHZAIJZKZGZGADEFZDCEFZACEFU
    SUTVBVDVBADLFZKUSUTGZVDVAVFAMNVGVFVDUQUTVFVDOZURUQUTGZADPFZVHVIABPFZUQVJUQU
    TVKUQBQJUTVKRBDESUAABQUBUCUKUQUTUDABDUETADUFUGUHULUIUJURVEUQVCCDUMUNUOADCUP
    T $.
    $( [19-Oct-2014] $)

  ${
    $d A x y z $.  $d ph x y z $.  $d B x y z $.  $d D y z $.  $d E x $.
    fiphp3d.a $e |- ( ph -> A ~~ NN ) $.
    fiphp3d.b $e |- ( ph -> B e. Fin ) $.
    fiphp3d.c $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    $( Infinite pigeonhole principle for partitioning an infinite set between
       finitely many buckets. $)
    fiphp3d $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN ) $=
      ( cv wceq crab cfn wcel wrex cn cen wbr com wa wn wral ominf risset eqcom
      ciun rexbii bitri sylib ralrimiva rabid2 sylibr iunrab syl6reqr eleq1d wb
      cvv omex nnenom entr sylancl enfi sylancr bitrd mtbiri iunfi sylan rexnal
      mtand wss jctir ssrab2 jctl ctbnfien syl2an ex reximdv mpd ) AFCJZKZBDLZM
      NZUAZCEOZWAPQRZCEOAWBCEUBZUAWDAWFCEWAUFZMNZAWHSMNZUCAWHDMNZWIAWGDMADVTCEO
      ZBDLZWGAWKBDUBDWLKAWKBDABJDNTFENZWKIWMVSFKZCEOWKCFEUDWNVTCEVSFUEUGUHUIUJW
      KBDUKULVTCBEDUMUNUOASUQNDSQRZWJWIUPURADPQRPSQRZWOGUSDPSUTVAZDSUQVBVCVDVEA
      EMNWFWHHCEWAVFVGVIWBCEVHULAWCWECEAWCWEAWOWPTWADVJZWCTWEWCAWOWPWQUSVKWCWRV
      TBDVLVMWADPVNVOVPVQVR $.
      $( [18-Oct-2014] $)
  $}

  ${
    $d A x y z $.  $d ph x y z $.  $d B x y z $.  $d D y z $.  $d E x $.
    fiphp3dOLD.1 $e |- ( ph -> A ~~ NN ) $.
    fiphp3dOLD.2 $e |- ( ph -> B e. Fin ) $.
    fiphp3dOLD.3 $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    fiphp3dOLD.4 $e |- ( x = z -> D = E ) $.
    $( Infinite pigeonhole principle for partitioning an infinite set between
       finitely many buckets.  This one can definitely be proven without AC.
       TODO $)
    fiphp3dOLD $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN ) $=
      ( fiphp3d ) ABCEFGIJKM $.
      $( [18-Oct-2014] $)
  $}

  ${
    $( Value of the numeric cardinality of a nonempty integer range. $)
    hashfz $p |- ( ( A e. ZZ /\ B e. ZZ /\ A <_ B ) -> ( # ` ( A ... B ) ) = (
        ( B - A ) + 1 ) ) $=
      ( cz wcel cle wbr cfz co chash cfv c1 caddc wceq syl2anc syl3anc wb cc cr
      a1i cc0 w3a cmin cen simp1 simp2 zsubcl fzen cfn fzfi hashen mp2an sylibr
      zre 3ad2ant1 recnd 1re subcl addcom npcan eqtrd 3ad2ant2 addsub12 oveq12d
      1z zcn fveq2d cn0 peano2zdi 0re resubcl readdcl addid1 syl eqbrtrd pncan3
      simp3 eqcomd oveq2d breqtrd leadd2 mpbird 1nn0 nn0ge0i mpbii letrd elnn0z
      wa sylanbrc hashfz1 3eqtrd ) ACDZBCDZABEFZUAZABGHZIJZAKAUBHZLHZBWQLHZGHZI
      JZKBAUBHZKLHZGHZIJZXCWNWOWTUCFZWPXAMZWNWKWLWQCDZXFWKWLWMUDZWKWLWMUEZWNKCD
      ZWKXHXKWNVDSXIKAUFNWQABUGOWOUHDWTUHDXGXFPABUIWRWSUIWOWTUJUKULWNWTXDIWNWRK
      WSXCGWNWRWQALHZKWNAQDZWQQDZWRXLMWNAWKWLARDZWMAUMUNZUOZWNKQDZXMXNWNKKRDZWN
      UPSZUOZXQKAUQNAWQURNWNXRXMXLKMYAXQKAUSNUTWNWSKXBLHZXCWNBQDZXRXMWSYBMWLWKY
      CWMBVEVAZYAXQBKAVBOWNXRXBQDZYBXCMYAWNYCXMYEYDXQBAUQNZKXBURNUTVCVFWNXCVGDZ
      XEXCMWNXCCDTXCEFYGWNXBWNWLWKXBCDXJXIBAUFNVHWNTXBTLHZXCTRDZWNVISZWNXBRDZYI
      YHRDZWNBRDZXOYKWLWKYMWMBUMVAXPBAVJNZYJXBTVKNZWNYKXSXCRDYNXTXBKVKNWNTYHEFZ
      ATLHZAYHLHZEFZWNYQBYREWNYQABEWNXMYQAMXQAVLVMWKWLWMVPVNWNBAXBLHZYRWNXMYCBY
      TMXQYDXMYCWGYTBABVOVQNWNXBYHALWNYHXBWNYEYHXBMYFXBVLVMVQVRUTVSWNYIYLXOYPYS
      PYJYOXPTYHAVTOWAWNTKEFZYHXCEFZKWBWCWNYIXSYKUUAUUBPYJXTYNTKXBVTOWDWEXCWFWH
      XCWIVMWJ $.
      $( [12-Sep-2014] $)

    $( Condition for finite ranges to have a strict dominance relation. $)
    fzsdom2 $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A <_ B -> ( B < C ->
        ( A ... B ) ~< ( A ... C ) ) ) ) $=
      ( cz wcel w3a cle wbr clt cfz co chash cfv cmin c1 cr wb 3ad2ant1 syl3anc
      zre caddc simp3 3ad2ant2 3ad2ant3 ltsub1 mpbid resubcl syl2anc 1re ltadd1
      csdm a1i wceq simp11 simp12 simp2 hashfz simp13 ltle imp syl21anc 3brtr4d
      wa letrd cfn fzfi hashsdom mp2an sylib 3exp ) ADEZBDEZCDEZFZABGHZBCIHZABJ
      KZACJKZUKHZVNVOVPFZVQLMZVRLMZIHZVSVTBANKZOUAKZCANKZOUAKZWAWBIVTWDWFIHZWEW
      GIHZVTVPWHVNVOVPUBZVTBPEZCPEZAPEZVPWHQVNVOWKVPVLVKWKVMBTUCRZVNVOWLVPVMVKW
      LVLCTUDRZVNVOWMVPVKVLWMVMATRRZBCAUESUFVTWDPEZWFPEZOPEZWHWIQVTWKWMWQWNWPBA
      UGUHVTWLWMWRWOWPCAUGUHWSVTUIULWDWFOUJSUFVTVKVLVOWAWEUMVKVLVMVOVPUNZVKVLVM
      VOVPUOVNVOVPUPZABUQSVTVKVMACGHWBWGUMWTVKVLVMVOVPURVTABCWPWNWOXAVTWKWLVPBC
      GHZWNWOWJWKWLVCVPXBBCUSUTVAVDACUQSVBVQVEEVRVEEWCVSQABVFACVFVQVRVGVHVIVJ
      $.
      $( [12-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    A non-closed set of reals is infinite
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b c d x y $.  $d B a b c d x y $.
    $( Lemma for ~ rencldnfilem . $)
    rencldnfilem $p |- ( ( ( A C_ RR /\ B e. RR /\ ( A =/= (/) /\ -. B e. A ) )
        /\ A. x e. RR+ E. y e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin ) $=
      ( va vb vc vd cr wcel wn wa cv clt wbr wrex crp wral wceq syl2anc wss wne
      c0 w3a cmin co cabs cfv cfn wi crab ccnv csup weq eqeq1 rexbidv elrab cc0
      cc simpl ad3antrrr simpr sseldd recnd subcl simprr ad2antrr nelneq subeq0
      necon3abid mpbird absrpcl eleq1 syl5ibrcom rexlimdva expimpd syl5bi ssrdv
      wb adantr cab abrexfi df-rab ss2abi eqsstri sylancl adantl wex simplrl n0
      ssfi sylib simpll simplr abscl syl eqid oveq1 fveq2d eqeq2d rcla4ev mpan2
      sylanbrc ne0i exlimdv mpd ssrab2 a1i ltso cnvso mpbi fisup2g mpan syl3anc
      ex wor cle mp2 fisupg sseli vex brcnv notbii lenlt biimprd adantll sylan2
      soss ralimdva adantrd reximdva lbinfmle sseldi mpbid breq2 notbid ralbidv
      ralrimiva ralnex rexbii rexnal bitri 3impa con2d imp ) CIUAZDIJZCUCUBZDCJ
      KZLZUDZBMZDUEUFZUGUHZAMZNOZBCPZAQRZCUIJZKUUKUUSUURUUFUUGUUJUUSUURKZUJUUFU
      UGLZUUJLZUUSUUTUVBUUSLZUUPKZBCRZAQPZUUTUVCEMZFMZDUEUFZUGUHZSZFCPZEIUKZINU
      LZUMZQJUUNUVONOZKZBCRZUVFUVCUVMQUVOUVBUVMQUAUUSUVBGUVMQGMZUVMJZUVSIJZUVSU
      VJSZFCPZLUVBUVSQJZUVLUWCEUVSIEGUNUVKUWBFCUVGUVSUVJUOUPUQUVBUWAUWCUWDUVBUW
      ALZUWBUWDFCUWEUVHCJZLZUWDUWBUVJQJZUWGUVIUSJZUVIURUBZUWHUWGUVHUSJZDUSJZUWI
      UWGUVHUWGCIUVHUVAUUFUUJUWAUWFUUFUUGUTVAUWEUWFVBZVCVDZUWGDUVAUUGUUJUWAUWFU
      UFUUGVBVAVDZUVHDVETUWGUWJUVHDSZKZUWGUWFUUIUWQUWMUVBUUIUWAUWFUVAUUHUUIVFVG
      UVHDCVHTUWGUWKUWLUWJUWQVSUWNUWOUWKUWLLUWPUVIURUVHDVIVJTVKUVIVLTUVSUVJQVMV
      NVOVPVQVRVTUVCUVMUIJZUVMUCUBZUVMIUAZUVOUVMJZUUSUWRUVBUUSUVLEWAZUIJUVMUXBU
      AUWRFECUVJWBUVMUVGIJZUVLLZEWAUXBUVLEIWCUXDUVLEUXCUVLVBWDWEUXBUVMWKWFWGZUV
      CUULCJZBWHZUWSUVCUUHUXGUVAUUHUUIUUSWIBCWJWLUVCUXFUWSBUVCUXFUWSUVCUXFLZUUN
      UVMJZUWSUXHUUNIJZUUNUVJSZFCPZUXIUXHUUMUSJZUXJUXHUULUSJUWLUXMUXHUULUXHCIUU
      LUVBUUFUUSUXFUUFUUGUUJWMVGUVCUXFVBVCVDUXHDUVBUUGUUSUXFUUFUUGUUJWNVGVDUULD
      VETUUMWOWPZUXFUXLUVCUXFUUNUUNSZUXLUUNWQUXKUXOFUULCFBUNZUVJUUNUUNUXPUVIUUM
      UGUVHUULDUEWRWSWTXAXBWGUVLUXLEUUNIUVGUUNSUVKUXKFCUVGUUNUVJUOUPUQXCZUVMUUN
      XDWPXOXEXFZUWTUVCUVLEIXGZXHIUVNXPZUWRUWSUWTUDUXAINXPUXTXIINXJXKZIUVMUVNXL
      XMXNZVCUVCUVQBCUXHUVOUUNXQOZUVQUXHUWTUVSHMZXQOZHUVMRZGUVMPZUXIUYCUWTUXHUX
      SXHUVCUYGUXFUVCUVSUYDUVNOZKZHUVMRZUYDUVSUVNOUYDUUOUVNOAUVMPUJHUVMRZLZGUVM
      PZUYGUVCUVMUVNXPZUWRUWSUYMUYNUVCUWTUXTUYNUXSUYAUVMIUVNYHXRXHUXEUXRGHAUVMU
      VNXSXNUVCUYLUYFGUVMUVTUVCUWAUYLUYFUJUVMIUVSUXSXTUVCUWALZUYJUYFUYKUYOUYIUY
      EHUVMUYDUVMJUYOUYDIJZUYIUYEUJZUVMIUYDUXSXTUWAUYPUYQUVCUYIUYDUVSNOZKZUWAUY
      PLZUYEUYHUYRUVSUYDNGYAHYAYBYCUYTUYEUYSUVSUYDYDYEVQYFYGYIYJYGYKXFVTUXQGHUU
      NUVMYLXNUXHUVOIJZUXJUYCUVQVSUVCVUAUXFUVCUVMIUVOUXSUYBYMVTUXNUVOUUNYDTYNYR
      UVEUVRAUVOQUUOUVOSZUVDUVQBCVUBUUPUVPUUOUVOUUNNYOYPYQXATUVFUUQKZAQPUUTUVEV
      UCAQUUPBCYSYTUUQAQUUAUUBWLXOUUCUUDUUE $.
      $( [18-Oct-2014] $)

    $( A set of real numbers which comes arbitrarily close to some target yet
       excludes it is infinite.  The work is done in ~ rencldnfilem using
       infima; this theorem removes the requirement that A be non-empty. $)
    rencldnfi $p |- ( ( ( A C_ RR /\ B e. RR /\ -. B e. A ) /\ A. x e. RR+ E. y
        e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin ) $=
      ( cr wss wcel wn w3a cv cmin co cabs cfv crp wral wa c0 wne c1 clt simpl1
      wbr wrex cfn simpl2 ralimi wb 1rp ne0i r19.3rzv mp2b sylibr adantl simpl3
      rexn0 jca simpr rencldnfilem syl31anc ) CEFZDEGZDCGHZIZBJDKLMNAJUAUCZBCUD
      ZAOPZQZVAVBCRSZVCQVGCUEGHVAVBVCVGUBVAVBVCVGUFVHVIVCVGVIVDVGVIAOPZVIVFVIAO
      VEBCUPUGTOGORSVIVJUHUIOTUJVIAOUKULUMUNVAVBVCVGUOUQVDVGURABCDUSUT $.
      $( [19-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Properties of the canonical representation of a rational
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c numer denom $.

  $( Extend class notation to include canonical numerator function. $)
  cnumer $a class numer $.
  $( Extend class notation to include canonical denominator function. $)
  cdenom $a class denom $.

  ${
    $d x y $.
    $( The canonical numerator of a rational is the numerator of the rational's
       reduced fraction representation (no common factors, denominator
       positive). $)
    df-numer $a |- numer = ( y e. QQ |-> ( 1st ` ( iota_ x e. ( ZZ X. NN ) ( (
        ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ y = ( ( 1st ` x ) / ( 2nd ` x ) )
        ) ) ) ) $.
    $( The canonical denominator of a rational is the denominator of the
       rational's reduced fraction representation (no common factors,
       denominator positive). $)
    df-denom $a |- denom = ( y e. QQ |-> ( 2nd ` ( iota_ x e. ( ZZ X. NN ) ( (
        ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ y = ( ( 1st ` x ) / ( 2nd ` x ) )
        ) ) ) ) $.
  $}

  ${
    $d A a b c d $.  $d B a b c d $.  $d C a b c d $.  $d x y a b c d $.

    ${
      $d A x $.
      $( Value of the canonical numerator function. $)
      qnumval $p |- ( A e. QQ -> ( numer ` A ) = ( 1st ` ( iota_ x e. ( ZZ X.
          NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ A = ( ( 1st ` x ) / (
          2nd ` x ) ) ) ) ) ) $=
        ( va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp cq cnumer eqeq1
        crio anbi2d riotabidv fveq2d df-numer fvex fvmpt ) CBADZEFZUGGFZHIJKZCD
        ZUHUILIZKZMZANOPZTZEFUJBULKZMZAUOTZEFQRUKBKZUPUSEUTUNURAUOUTUMUQUJUKBUL
        SUAUBUCACUDUSEUEUF $.
        $( [13-Sep-2014] $)

      $( Value of the canonical denominator function. $)
      qdenval $p |- ( A e. QQ -> ( denom ` A ) = ( 2nd ` ( iota_ x e. ( ZZ X.
          NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ A = ( ( 1st ` x ) / (
          2nd ` x ) ) ) ) ) ) $=
        ( va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp cq cdenom eqeq1
        crio anbi2d riotabidv fveq2d df-denom fvex fvmpt ) CBADZEFZUGGFZHIJKZCD
        ZUHUILIZKZMZANOPZTZGFUJBULKZMZAUOTZGFQRUKBKZUPUSGUTUNURAUOUTUMUQUJUKBUL
        SUAUBUCACUDUSGUEUF $.
        $( [13-Sep-2014] $)
    $}

    $( Lemma for ~ qnumcl and ~ qdencl . $)
    qnumdencl $p |- ( A e. QQ -> ( ( numer ` A ) e. ZZ /\ ( denom ` A ) e. NN )
        ) $=
      ( va cq wcel cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cnumer eleq1d
      cxp crio cdenom wreu qredeu riotacl syl cop elxp6 qnumval qdenval anbi12d
      biimprd adantld syl5bi mpd ) ACDZBEZFGZUPHGZIJKLAUQURMJLNZBOPSZTZUTDZAQGZ
      ODZAUAGZPDZNZUOUSBUTUBVBBAUCUSBUTUDUEVBVAVAFGZVAHGZUFLZVHODZVIPDZNZNUOVGV
      AOPUGUOVMVGVJUOVGVMUOVDVKVFVLUOVCVHOBAUHRUOVEVIPBAUIRUJUKULUMUN $.
      $( [13-Sep-2014] $)

    $( The canonical numerator of a rational is an integer. $)
    qnumcl $p |- ( A e. QQ -> ( numer ` A ) e. ZZ ) $=
      ( cq wcel cnumer cfv cz cdenom cn qnumdencl simpld ) ABCADEFCAGEHCAIJ $.
      $( [13-Sep-2014] $)

    $( The canonical denominator is a positive integer. $)
    qdencl $p |- ( A e. QQ -> ( denom ` A ) e. NN ) $=
      ( cq wcel cnumer cfv cz cdenom cn qnumdencl simprd ) ABCADEFCAGEHCAIJ $.
      $( [13-Sep-2014] $)

    $( Canonical numerator defines a function. $)
    fnum $p |- numer : QQ --> ZZ $=
      ( vb va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp crio cq cnumer
      wcel wf wral df-numer fmpt biimpi qnumval qnumcl eqeltrrd mprg ) ACZDEZUI
      FEZGHIJBCZUJUKKHJLAMNOPDEZMSZQMRTZBQUNBQUAUOBQMUMRABUBUCUDULQSULREUMMAULU
      EULUFUGUH $.
      $( [13-Sep-2014] $)

    $( Canonical denominator defines a function. $)
    fden $p |- denom : QQ --> NN $=
      ( vb va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp crio cq cdenom
      wcel wf wral df-denom fmpt biimpi qdenval qdencl eqeltrrd mprg ) ACZDEZUI
      FEZGHIJBCZUJUKKHJLAMNOPFEZNSZQNRTZBQUNBQUAUOBQNUMRABUBUCUDULQSULREUMNAULU
      EULUFUGUH $.
      $( [13-Sep-2014] $)

    $( Two numbers are the canonical representation of a rational iff they are
       coprime and have the right quotient. $)
    qnumdenbi $p |- ( ( A e. QQ /\ B e. ZZ /\ C e. NN ) -> ( ( ( B gcd C ) = 1
        /\ A = ( B / C ) ) <-> ( ( numer ` A ) = B /\ ( denom ` A ) = C ) ) )
        $=
      ( va wcel cz cn cfv wceq wa c1st c2nd cgcd co c1 cdiv cop eqeq1d oveq12d
      wb vb w3a cnumer cdenom cxp crio wreu qredeu riotacl 1st2nd2 3syl qnumval
      cq cv qdenval opeq12d eqtr4d 3ad2ant1 fvex opthg 3ad2ant3 opelxpi 3adant1
      bitr2d ax-17 a17d eqeq2d anbi12d riota2f syl2anc op1stg 3ad2ant2 3bitr2rd
      fveq2 op2ndg ) AUMEZBFEZCGEZUBZAUCHZBIAUDHZCIJZDUNZKHZWCLHZMNZOIZAWDWEPNZ
      IZJZDFGUEZUFZBCQZIZWMKHZWMLHZMNZOIZAWOWPPNZIZJZBCMNZOIZABCPNZIZJVSWNVTWAQ
      ZWMIZWBVPVQWNXGTVRVPWLXFWMVPWLWLKHZWLLHZQZXFVPWJDWKUGZWLWKEWLXJIDAUHZWJDW
      KUIWLFGUJUKVPVTXHWAXIDAULDAUOUPUQRURVRVPXGWBTVQVTWABCGAUCUSAUDUSUTVAVDVSW
      MWKEZXKXAWNTVQVRXMVPBCFGVBVCVPVQXKVRXLURWJXADUAWKWMUAUNWMEDVEXMXADVFWCWMI
      ZWGWRWIWTXNWFWQOXNWDWOWEWPMWCWMKVNZWCWMLVNZSRXNWHWSAXNWDWOWEWPPXOXPSVGVHV
      IVJVSWRXCWTXEVSWQXBOVSWOBWPCMVQVPWOBIVRBCFVKVLZVQVRWPCIVPBCFGVOVCZSRVSWSX
      DAVSWOBWPCPXQXRSVGVHVM $.
      $( [13-Sep-2014] $)

    $( The canonical representation of a rational is fully reduced. $)
    qnumdencoprm $p |- ( A e. QQ -> ( ( numer ` A ) gcd ( denom ` A ) ) = 1 )
        $=
      ( cq wcel cnumer cfv cdenom cgcd co c1 wceq wa eqidd eqid1 jctir cz cn wb
      cdiv qnumcl qdencl qnumdenbi mpd3an23 mpbird simpld ) ABCZADEZAFEZGHIJZAU
      FUGRHJZUEUHUIKZUFUFJZUGUGJZKZUEUKULUEUFLUGMNUEUFOCUGPCUJUMQASATAUFUGUAUBU
      CUD $.
      $( [13-Sep-2014] $)

    $( Recover a rational number from its canonical representation. $)
    qeqnumdivden $p |- ( A e. QQ -> A = ( ( numer ` A ) / ( denom ` A ) ) ) $=
      ( cq wcel cnumer cfv cdenom cgcd co c1 wceq wa eqidd eqid1 jctir cz cn wb
      cdiv qnumcl qdencl qnumdenbi mpd3an23 mpbird simprd ) ABCZADEZAFEZGHIJZAU
      FUGRHJZUEUHUIKZUFUFJZUGUGJZKZUEUKULUEUFLUGMNUEUFOCUGPCUJUMQASATAUFUGUAUBU
      CUD $.
      $( [13-Sep-2014] $)

    $( Multiplying a rational by its denominator results in an integer. $)
    qmuldeneqnum $p |- ( A e. QQ -> ( A x. ( denom ` A ) ) = ( numer ` A ) ) $=
      ( cq wcel cdenom cfv cmul co cnumer cdiv qeqnumdivden oveq1d cc0 wne wceq
      cc cz qnumcl zcn syl cn qdencl nncn nnne0 divcan1 syl3anc eqtrd ) ABCZAAD
      EZFGAHEZUHIGZUHFGZUIUGAUJUHFAJKUGUIOCZUHOCZUHLMZUKUINUGUIPCULAQUIRSUGUHTC
      ZUMAUAZUHUBSUGUOUNUPUHUCSUIUHUDUEUF $.
      $( [13-Sep-2014] $)

    $( A number is an integer iff its negative is. $)
    znegclb $p |- ( A e. CC -> ( A e. ZZ <-> -u A e. ZZ ) ) $=
      ( cc wcel cz cneg znegcl negneg eleq1d syl5ib impbid2 ) ABCZADCZAEZDCZAFN
      MEZDCKLMFKOADAGHIJ $.
      $( [13-Sep-2014] $)

    $( A number which is less than zero is not zero. $)
    lt0ne0 $p |- ( ( A e. RR /\ A < 0 ) -> A =/= 0 ) $=
      ( cr wcel cc0 clt wbr wa wne 0re ltne mp3an2 necomd ) ABCZADEFZGDAMDBCNDA
      HIADJKL $.
      $( [13-Sep-2014] $)

    $( Strong form of ~ divides2 for natural numbers. $)
    nndivdivides $p |- ( ( A e. NN /\ B e. NN ) -> ( B || A <-> ( A / B ) e. NN
        ) ) $=
      ( cn wcel wa cdivides wbr cc0 cdiv co clt cz wne wb adantl adantr cr nnre
      nnz nngt0 nnne0 divides2 syl3anc anbi1d divgt0 syl22anc elnnz a1i 3bitr4d
      biantrud ) ACDZBCDZEZBAFGZHABIJZKGZEUOLDZUPEZUNUOCDZUMUNUQUPUMBLDZBHMZALD
      ZUNUQNULUTUKBSOULVAUKBUAOUKVBULASPBAUBUCUDUMUPUNUMAQDZHAKGZBQDZHBKGZUPUKV
      CULARPUKVDULATPULVEUKBROULVFUKBTOABUEUFUJUSURNUMUOUGUHUI $.
      $( [13-Sep-2014] $)

    $( Calculate the reduced form of a quotient using ` gcd ` . $)
    divnumden $p |- ( ( A e. ZZ /\ B e. NN ) -> ( ( numer ` ( A / B ) ) = ( A /
        ( A gcd B ) ) /\ ( denom ` ( A / B ) ) = ( B / ( A gcd B ) ) ) ) $=
      ( cz wcel cn wa cgcd co cdiv wceq cfv cdivides wbr adantl syl2anc cc0 syl
      c1 wb cc cnumer cdenom cq znq simpl nnz gcddvds simpld wne cn0 gcdcl nn0z
      sylan2 nnne0 df-ne sylib intnand gcdn0cl syl21anc divides2 syl3anc simprd
      wn mpbid simpr nndivdivides qnumdenbi gcddiv syl31anc divid eqtr3d adantr
      nncn zcn w3a divcan7 eqcomd syl122anc mpbi2and ) ACDZBEDZFZAABGHZIHZBWCIH
      ZGHZRJZABIHZWDWEIHZJZWHUAKWDJWHUBKWEJFZWBWHUCDWDCDZWEEDZWGWJFWKSABUDWBWCA
      LMZWLWBWNWCBLMZWBVTBCDZWNWOFZVTWAUEZWAWPVTBUFZNZABUGOZUHWBWCCDZWCPUIZVTWN
      WLSWAVTWPXBWSVTWPFWCUJDXBABUKWCULQUMWBWCEDZXCWBVTWPAPJZBPJZFVCXDWRWTWBXFX
      EWAXFVCZVTWABPUIZXGBUNZBPUOUPNUQABURUSZWCUNQZWRWCAUTVAVDWBWOWMWBWNWOXAVBW
      BWAXDWOWMSVTWAVEXJBWCVFOVDWHWDWEVGVAWBWCWCIHZWFRWBVTWPXDWQXLWFJWRWTXJXAAB
      WCVHVIWBWCTDZXCXLRJWBXDXMXJWCVMQZXKWCVJOVKWBATDZBTDZXHXMXCWJVTXOWAAVNVLWA
      XPVTBVMNWAXHVTXINXNXKXOXPXHFXMXCFVOWIWHABWCVPVQVRVS $.
      $( [13-Sep-2014] $)

    $( Reducing a quotient never increases the denominator. $)
    divdenle $p |- ( ( A e. ZZ /\ B e. NN ) -> ( denom ` ( A / B ) ) <_ B ) $=
      ( cz wcel cn wa cdiv co cfv cle wceq c1 wbr cc0 wn adantl syl cr clt a1i
      cdenom cgcd cnumer divnumden simprd simpl nnz nnne0 df-ne intnand gcdn0cl
      wne sylib syl21anc nnge1 wb 1re lt01 nnre nngt0 lediv2 syl222anc mpbid cc
      nncn div1 breqtrd eqbrtrd ) ACDZBEDZFZABGHZUAIZBABUBHZGHZBJVKVLUCIAVNGHKV
      MVOKABUDUEVKVOBLGHZBJVKLVNJMZVOVPJMZVKVNEDZVQVKVIBCDZANKZBNKZFOVSVIVJUFVJ
      VTVIBUGPVKWBWAVJWBOZVIVJBNULWCBUHBNUIUMPUJABUKUNZVNUOQVKLRDZNLSMZVNRDZNVN
      SMZBRDZNBSMZVQVRUPWEVKUQTWFVKURTVKVSWGWDVNUSQVKVSWHWDVNUTQVJWIVIBUSPVJWJV
      IBUTPLVNBVAVBVCVKBVDDZVPBKVJWKVIBVEPBVFQVGVH $.
      $( [13-Sep-2014] $)

    $( A rational is positive iff its canonical numerator is. $)
    qnumgt0 $p |- ( A e. QQ -> ( 0 < A <-> 0 < ( numer ` A ) ) ) $=
      ( cq wcel cc0 clt wbr cdenom cfv cmul co cnumer cr wb 0re a1i qre cn nnre
      qdencl syl nngt0 ltmul1 syl112anc cc wceq nncn mul02 qmuldeneqnum breq12d
      3syl bitrd ) ABCZDAEFZDAGHZIJZAUNIJZEFZDAKHZEFULDLCZALCUNLCZDUNEFZUMUQMUS
      ULNOAPULUNQCZUTASZUNRTULVBVAVCUNUATDAUNUBUCULUODUPUREULVBUNUDCUODUEVCUNUF
      UNUGUJAUHUIUK $.
      $( [15-Sep-2014] $)

    $( A rational is positive iff its canonical numerator is a natural
       number. $)
    qgt0numnn $p |- ( ( A e. QQ /\ 0 < A ) -> ( numer ` A ) e. NN ) $=
      ( cq wcel cc0 clt wbr wa cnumer cfv cz qnumcl adantr qnumgt0 biimpa elnnz
      cn sylanbrc ) ABCZDAEFZGAHIZJCZDTEFZTPCRUASAKLRSUBAMNTOQ $.
      $( [15-Sep-2014] $)

    $( The square of a rational is rational. $)
    qsqcl $p |- ( A e. QQ -> ( A ^ 2 ) e. QQ ) $=
      ( cq wcel c2 cexp co cmul cc wceq qcn sqval syl qmulcl anidms eqeltrd ) A
      BCZADEFZAAGFZBPAHCQRIAJAKLPRBCAAMNO $.
      $( [15-Sep-2014] $)

    $( Squaring commutes with GCD, in particular two coprime numbers have
       coprime squares. $)
    nn0gcdsq $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( ( A gcd B ) ^ 2 ) = ( ( A ^
        2 ) gcd ( B ^ 2 ) ) ) $=
      ( cn0 wcel cn cc0 wceq wo cgcd co c2 cexp wa cabs cfv syl cz oveq1d oveq1
      sq0 elnn0 sqgcd nncn abssq nnz gcd0id a1i zsqcl 3syl eqtrd 3eqtr4d adantl
      cc eqeq12d adantr mpbird gcdid0 oveq2d oveq2 gcd0val oveq1i oveq12i eqtri
      wb 3eqtr4i oveq12 oveqan12d 3eqtr4a ccase syl2anb ) ACDAEDZAFGZHBEDZBFGZH
      ABIJZKLJZAKLJZBKLJZIJZGZBCDAUABUAVKVMVLVNVTABUBVLVMMVTFBIJZKLJZFKLJZVRIJZ
      GZVMWEVLVMBNOZKLJZVRNOZWBWDVMBUMDWGWHGBUCBUDPVMWAWFKLVMBQDZWAWFGBUEZBUFPR
      VMWDFVRIJZWHVMWCFVRIWCFGZVMTUGRVMWIVRQDWKWHGWJBUHVRUFUIUJUKULVLVTWEVDVMVL
      VPWBVSWDVLVOWAKLAFBISRVLVQWCVRIAFKLSZRUNUOUPVKVNMVTAFIJZKLJZVQWCIJZGZVKWQ
      VNVKANOZKLJZVQNOZWOWPVKAUMDWSWTGAUCAUDPVKWNWRKLVKAQDZWNWRGAUEZAUQPRVKWPVQ
      FIJZWTVKWCFVQIWLVKTUGURVKXAVQQDXCWTGXBAUHVQUQUIUJUKUOVNVTWQVDVKVNVPWOVSWP
      VNVOWNKLBFAIUSRVNVRWCVQIBFKLSZURUNULUPVLVNMZFFIJZKLJZWCWCIJZVPVSWCFXGXHTX
      FFKLUTVAXHXFFWCFWCFITTVBUTVCVEXEVOXFKLAFBFIVFRVLVNVQWCVRWCIWMXDVGVHVIVJ
      $.
      $( [15-Sep-2014] $)

    $( ~ nn0gcdsq extended to integers by symmetry. $)
    zgcdsq $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A gcd B ) ^ 2 ) = ( ( A ^ 2 )
        gcd ( B ^ 2 ) ) ) $=
      ( cz wcel wa cgcd co c2 cexp cabs cfv gcdabs eqcomd cn0 wceq nn0abscl zre
      cr absresq syl oveq1d nn0gcdsq syl2an adantr adantl oveq12d 3eqtrd ) ACDZ
      BCDZEZABFGZHIGAJKZBJKZFGZHIGZULHIGZUMHIGZFGZAHIGZBHIGZFGUJUKUNHIUJUNUKABL
      MUAUHULNDUMNDUOUROUIAPBPULUMUBUCUJUPUSUQUTFUJARDZUPUSOUHVAUIAQUDASTUJBRDZ
      UQUTOUIVBUHBQUEBSTUFUG $.
      $( [15-Sep-2014] $)

    $( Squaring a rational squares its canonical components. $)
    numdensq $p |- ( A e. QQ -> ( ( numer ` ( A ^ 2 ) ) = ( ( numer ` A ) ^ 2 )
        /\ ( denom ` ( A ^ 2 ) ) = ( ( denom ` A ) ^ 2 ) ) ) $=
      ( cq wcel cnumer cfv c2 cexp co cdenom cgcd c1 wceq cdiv wa cz cn syl3anc
      syl oveq1d cc qsqcl qnumcl zsqcl qdencl nnsqcl qnumdenbi qnumdencoprm nnz
      zgcdsq syl2anc sq1 a1i 3eqtr3d qeqnumdivden cc0 wne zcn nnne0 sqdiv eqtrd
      wb nncn mpbi2and ) ABCZADEZFGHZAIEZFGHZJHZKLZAFGHZVFVHMHZLZVKDEVFLVKIEVHL
      NZVDVKBCVFOCZVHPCZVJVMNVNVAAUAVDVEOCZVOAUBZVEUCRVDVGPCZVPAUDZVGUERVKVFVHU
      FQVDVEVGJHZFGHZKFGHZVIKVDWAKFGAUGSVDVQVGOCZWBVILVRVDVSWDVTVGUHRVEVGUIUJWC
      KLVDUKULUMVDVKVEVGMHZFGHZVLVDAWEFGAUNSVDVETCZVGTCZVGUOUPZWFVLLVDVQWGVRVEU
      QRVDVSWHVTVGVBRVDVSWIVTVGURRVEVGUSQUTVC $.
      $( [15-Sep-2014] $)

    $( Square commutes with canonical numerator. $)
    numsq $p |- ( A e. QQ -> ( numer ` ( A ^ 2 ) ) = ( ( numer ` A ) ^ 2 ) ) $=
      ( cq wcel c2 cexp co cnumer cfv wceq cdenom numdensq simpld ) ABCADEFZGHA
      GHDEFIMJHAJHDEFIAKL $.
      $( [15-Sep-2014] $)

    $( Square commutes with canonical denominator. $)
    densq $p |- ( A e. QQ -> ( denom ` ( A ^ 2 ) ) = ( ( denom ` A ) ^ 2 ) ) $=
      ( cq wcel c2 cexp co cnumer cfv wceq cdenom numdensq simprd ) ABCADEFZGHA
      GHDEFIMJHAJHDEFIAKL $.
      $( [15-Sep-2014] $)

    $( A rational is an integer iff it has denominator 1. $)
    qden1elz $p |- ( A e. QQ -> ( ( denom ` A ) = 1 <-> A e. ZZ ) ) $=
      ( cq wcel cdenom cfv c1 wceq cz wa cnumer cdiv co adantr cc zcn div1 3syl
      cle wbr cn qeqnumdivden oveq2 adantl qnumcl 3eqtrd eqeltrd simpr divdenle
      fveq2d 1nn sylancl eqbrtrrd wb qdencl nnle1eq1 syl mpbid impbida ) ABCZAD
      EZFGZAHCZUSVAIZAAJEZHVCAVDUTKLZVDFKLZVDUSAVEGVAAUAMVAVEVFGUSUTFVDKUBUCVCV
      DHCZVDNCVFVDGUSVGVAAUDMZVDOVDPQUEVHUFUSVBIZUTFRSZVAVIAFKLZDEZUTFRVIVKADVI
      VBANCVKAGUSVBUGZAOAPQUIVIVBFTCVLFRSVMUJAFUHUKULVIUTTCZVJVAUMUSVNVBAUNMUTU
      OUPUQUR $.
      $( [15-Sep-2014] $)

    $( If an integer has a rational square root, that root is must be an
       integer. $)
    zsqrelqelz $p |- ( ( A e. ZZ /\ ( sqr ` A ) e. QQ ) -> ( sqr ` A ) e. ZZ )
        $=
      ( cz wcel cfv cq cdenom c1 wceq c2 cexp co a1i syl adantr qden1elz adantl
      wb cr cc0 cle csqr wa sq1 cc zcn sqrth fveq2d simpl zq mpbird eqtrd densq
      3eqtr2rd wbr qdencl nnre cn0 nnnn0 nn0ge0 3syl 1nn0 nn0ge0i sq11 syl22anc
      cn 1re mpbid ) ABCZAUADZECZUBZVIFDZGHZVIBCZVKVLIJKZGIJKZHZVMVKVPGVIIJKZFD
      ZVOVPGHVKUCLVKVSAFDZGVKVRAFVHVRAHZVJVHAUDCWAAUEAUFMNUGVKVTGHZVHVHVJUHVKAE
      CZWBVHQVHWCVJAUINAOMUJUKVJVSVOHVHVIULPUMVKVLRCZSVLTUNZGRCZSGTUNZVQVMQVKVL
      VECZWDVJWHVHVIUOPZVLUPMVKWHVLUQCWEWIVLURVLUSUTWFVKVFLWGVKGVAVBLVLGVCVDVGV
      JVMVNQVHVIOPVG $.
      $( [15-Sep-2014] $)

    $( Any integer strictly between two adjacent squares has an irrational
       square root. $)
    nonsq $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( ( B ^ 2 ) < A /\ A < ( ( B +
        1 ) ^ 2 ) ) ) -> -. ( sqr ` A ) e. QQ ) $=
      ( cn0 wcel wa c2 cexp co clt wbr cz nn0z ad2antlr cr ad2antrr syl cc0 cle
      nn0re nn0ge0 c1 caddc csqr cq wn simprl wceq recnd sqrth breqtrrd resqrcl
      cfv cc wb syl2anc sqrge0 lt2sq syl22anc mpbird eqbrtrd peano2re peano2nn0
      simprr btwnnz syl3anc wi zsqrelqelz ex mtod ) ACDZBCDZEZBFGHZAIJZABUAUBHZ
      FGHZIJZEZEZAUCULZUDDZVTKDZVSBKDZBVTIJZVTVOIJZWBUEVKWCVJVRBLMVSWDVMVTFGHZI
      JZVSVMAWFIVLVNVQUFVSAUMDWFAUGVSAVJANDZVKVRASOZUHAUIPZUJVSBNDZQBRJZVTNDZQV
      TRJZWDWGUNVKWKVJVRBSMZVKWLVJVRBTMVSWHQARJZWMWIVJWPVKVRATOZAUKUOZVSWHWPWNW
      IWQAUPUOZBVTUQURUSVSWEWFVPIJZVSWFAVPIWJVLVNVQVCUTVSWMWNVONDZQVORJZWEWTUNW
      RWSVSWKXAWOBVAPVKXBVJVRVKVOCDXBBVBVOTPMVTVOUQURUSBVTVDVEVSAKDZWAWBVFVJXCV
      KVRALOXCWAWBAVGVHPVI $.
      $( [15-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Miscellanea for Lagrange's theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Two elements in a half-open interval have separation _strictly_ less
       than the difference between the endpoints. $)
    icodiamlt $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. ( A [,) B ) /\ D e. (
        A [,) B ) ) ) -> ( abs ` ( C - D ) ) < ( B - A ) ) $=
      ( cr wcel wa co cmin clt wbr cle w3a elico2 wb resubcl syl2anc cc syl3anc
      mpbid cico cabs cfv cxr wi rexr anbi12d biimpd sylan2 cneg simprl1 simplr
      simprr1 simpll abslt wceq negsubdi2 simprl2 lesub1 simprr3 ltsub2 lelttrd
      recnd eqbrtrd simprl3 ltsub1 simprr2 lesub2 ltletrd mpbir2and ex syld imp
      ) AEFZBEFZGZCABUAHZFZDVQFZGZCDIHZUBUCBAIHZJKZVPVTCEFZACLKZCBJKZMZDEFZADLK
      ZDBJKZMZGZWCVOVNBUDFZVTWLUEBUFVNWMGZVTWLWNVRWGVSWKABCNABDNUGUHUIVPWLWCVPW
      LGZWCWBUJZWAJKZWAWBJKZWOWAEFZWBEFZWCWQWRGOWOWDWHWSWDWEWFWKVPUKZWHWIWJWGVP
      UMZCDPQZWOVOVNWTVNVOWLULZVNVOWLUNZBAPQZWAWBUOQWOWPABIHZWAJWOBRFARFWPXGUPW
      OBXDVCWOAXEVCBAUQQWOXGCBIHZWAWOVNVOXGEFXEXDABPQWOWDVOXHEFXAXDCBPQXCWOWEXG
      XHLKZWDWEWFWKVPURWOVNWDVOWEXIOXEXAXDACBUSSTWOWJXHWAJKZWHWIWJWGVPUTWOWHVOW
      DWJXJOXBXDXADBCVASTVBVDWOWABDIHZWBXCWOVOWHXKEFXDXBBDPQXFWOWFWAXKJKZWDWEWF
      WKVPVEWOWDVOWHWFXLOXAXDXBCBDVFSTWOWIXKWBLKZWHWIWJWGVPVGWOVNWHVOWIXMOXEXBX
      DADBVHSTVIVJVKVLVM $.
      $( [12-Sep-2014] $)

    $( Modular reduction produces a half-open interval. $)
    modelico $p |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) e. ( 0 [,) B ) ) $=
      ( cr wcel crp wa cmo co cc0 cico cle wbr clt cxr w3a wb 0re rpre rexr syl
      adantl elico2 sylancr modcl modge0 modlt mpbir3and ) ACDZBEDZFZABGHZIBJHD
      ZUKCDZIUKKLZUKBMLZUJICDBNDZULUMUNUOOPQUIUPUHUIBCDUPBRBSTUAIBUKUBUCABUDABU
      EABUFUG $.
      $( [12-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Lagrange's rational approximation theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x a b c $.  $d A a b c d x y z w $.  $d B a b c d x y z w $.
    $( Lemma for ~ irrapx1 .  Divides the unit interval into ` A ` half-open
       sections and using the pigeonhole principle ~ fphpdo finds two multiples
       of ` A ` in the same section mod 1. $)
    irrapxlem1 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. (
        0 ... B ) ( x < y /\ ( |_ ` ( B x. ( ( A x. x ) mod 1 ) ) ) = ( |_ ` (
        B x. ( ( A x. y ) mod 1 ) ) ) ) ) $=
      ( wcel cc0 co c1 cmul cmo cfl cr cz a1i cle wbr clt sylancl syl wb va crp
      cn wa cfz cmin cv cfv wss cuz fzssuz uzssz zssre sstri cvv ovex 0z adantl
      csdm nnz zsubcl cn0 simpr nnm1nn0 nn0ge0 3syl nnre ltm1 fzsdom2 syl311anc
      1z w3a 3imp ad2antlr rpre ad2antrr elfzelz zre remulcl syl2anc modcl flcl
      wn cc wceq recnd mul01 modge0 nngt0 lemul2 syl112anc mpbid eqbrtrrd lenlt
      1rp 0re fllt mtbid mpbird elnn0z sylanbrc caddc flle modlt ltmul2 breqtrd
      1re mulid1 lelttrd ax-1cn npcan breqtrrd zleltp1 elfz2nn0 ax-mp syl3anbrc
      nncn weq oveq2 oveq1d oveq2d fveq2d fphpdo ) CUBEZDUCEZUDZABUAFDUEGZFDHUF
      GZUEGZDCUAUGZIGZHJGZIGZKUHZDCAUGZIGZHJGZIGZKUHDCBUGZIGZHJGZIGZKUHYGLUIYFY
      GFUJUHZLFDUKUUCMLFULUMUNUNNYIUOEYFFYHUEUPNYFFMEZYHMEZDMEZFYHOPZYHDQPZYIYG
      USPZUUDYFUQNYFUUFHMEZUUEYEUUFYDDUTZURZVKDHVAZRUULYFYEYHVBEZUUGYDYEVCDVDZY
      HVEVFYFDLEZUUHYEUUPYDDVGZURDVHSUUDUUEUUFVLUUGUUHUUIFYHDVIVMVJYFYJYGEZUDZY
      NVBEZUUNYNYHOPZYNYIEZUUSYNMEZFYNOPZUUTUUSYMLEZUVCUUSUUPYLLEZUVEYEUUPYDUUR
      UUQVNZUUSYKLEZHUBEZUVFUUSCLEZYJLEZUVHYDUVJYEUURCVOVPUURUVKYFUURYJMEUVKYJF
      DVQYJVRSURCYJVSVTZWOYKHWARZDYLVSVTZYMWBSZUUSUVDYNFQPZWCZUUSYMFQPZUVPUUSFY
      MOPZUVRWCZUUSDFIGZFYMOUUSDWDEZUWAFWEUUSDUVGWFZDWGSUUSFYLOPZUWAYMOPZUUSUVH
      UVIUWDUVLWOYKHWHRUUSFLEZUVFUUPFDQPZUWDUWETUWFUUSWPNZUVMUVGYEUWGYDUURDWIVN
      ZFYLDWJWKWLWMUUSUWFUVEUVSUVTTUWHUVNFYMWNVTWLUUSUVEUUDUVRUVPTUVNUQYMFWQRWR
      UUSUWFYNLEZUVDUVQTUWHUUSUVCUWJUVOYNVRSZFYNWNVTWSYNWTXAYEUUNYDUURUUOVNUUSU
      VAYNYHHXBGZQPZUUSYNDUWLQUUSYNYMDUWKUVNUVGUUSUVEYNYMOPUVNYMXCSUUSYMDHIGZDQ
      UUSYLHQPZYMUWNQPZUUSUVHUVIUWOUVLWOYKHXDRUUSUVFHLEZUUPUWGUWOUWPTUVMUWQUUSX
      GNUVGUWIYLHDXEWKWLUUSUWBUWNDWEUWCDXHSXFXIYEUWLDWEZYDUURYEUWBHWDEUWRDXQXJD
      HXKRVNXLUUSUVCUUEUVAUWMTUVOUUSUUFUUJUUEYEUUFYDUURUUKVNVKUUMRYNYHXMVTWSYHU
      OEUVBUUTUUNUVAVLTDHUFUPUOYNYHXNXOXPUAAXRZYMYRKUWSYLYQDIUWSYKYPHJYJYOCIXSX
      TYAYBUABXRZYMUUBKUWTYLUUADIUWTYKYTHJYJYSCIXSXTYAYBYC $.
      $( [12-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Two multiples in the same bucket means they are
       very close mod 1. $)
    irrapxlem2 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. (
        0 ... B ) ( x < y /\ ( abs ` ( ( ( A x. x ) mod 1 ) - ( ( A x. y ) mod
        1 ) ) ) < ( 1 / B ) ) ) $=
      ( wcel wa clt wbr cmul co c1 cfv wceq cc0 cmin cabs cr syl2anc cc recnd
      crp cn cv cmo cfl cfz wrex cdiv irrapxlem1 nnre adantl ad2antrr ad3antrrr
      caddc rpre elfzelz zre syl ad2antlr remulcl 1rp a1i modcl intfrac oveq12d
      fveq2d adantr simpr oveq1d flcl zcn 3syl pnpcan syl3anc cico 0re modelico
      cz 1re icodiamlt syl22anc ax-1cn subid1i syl6breq eqbrtrd ex resubcl recn
      wb abscl wne nngt0 gt0ne0 redivcl ltmul2 syl112anc cle nnnn0 nn0ge0 absid
      eqcomd absmul subdi 3eqtr2d divcan2 breq12d bitrd sylibrd anim2d reximdva
      cn0 mpd ) CUAEZDUBEZFZAUCZBUCZGHZDCXPIJZKUDJZIJZUELZDCXQIJZKUDJZIJZUELZMZ
      FZBNDUFJZUGZAYIUGXRXTYDOJZPLZKDUHJZGHZFZBYIUGZAYIUGABCDUIXOYJYPAYIXOXPYIE
      ZFZYHYOBYIYRXQYIEZFZYGYNXRYTYGYAYEOJZPLZKGHZYNYTYGUUCYTYGFZUUBYBYAKUDJZUN
      JZYFYEKUDJZUNJZOJZPLZKGYTUUBUUJMYGYTUUAUUIPYTYAUUFYEUUHOYTYAQEZYAUUFMYTDQ
      EZXTQEZUUKXOUULYQYSXNUULXMDUJUKULZYTXSQEZKUAEZUUMYTCQEZXPQEZUUOXMUUQXNYQY
      SCUOUMZYQUURXOYSYQXPVREUURXPNDUPXPUQURUSCXPUTRUUPYTVAVBZXSKVCRZDXTUTRZYAV
      DURYTYEQEZYEUUHMYTUULYDQEZUVCUUNYTYCQEZUUPUVDYTUUQXQQEZUVEUUSYSUVFYRYSXQV
      REUVFXQNDUPXQUQURUKCXQUTRUUTYCKVCRZDYDUTRZYEVDURVEVFVGUUDUUJYFUUEUNJZUUHO
      JZPLZKGUUDUUIUVJPUUDUUFUVIUUHOUUDYBYFUUEUNYTYGVHVIVIVFYTUVKKGHYGYTUVKUUEU
      UGOJZPLZKGYTUVJUVLPYTYFSEZUUESEUUGSEUVJUVLMYTUVCYFVREUVNUVHYEVJYFVKVLYTUU
      EYTUUKUUPUUEQEUVBUUTYAKVCRTYTUUGYTUVCUUPUUGQEUVHUUTYEKVCRTYFUUEUUGVMVNVFY
      TUVMKNOJZKGYTNQEZKQEZUUENKVOJZEZUUGUVREZUVMUVOGHUVPYTVPVBUVQYTVSVBZYTUUKU
      UPUVSUVBUUTYAKVQRYTUVCUUPUVTUVHUUTYEKVQRNKUUEUUGVTWAKWBWCWDWEVGWEWEWFYTYN
      DYLIJZDYMIJZGHZUUCYTYLQEZYMQEZUULNDGHZYNUWDWIYTYKQEZYKSEZUWEYTUUMUVDUWHUV
      AUVGXTYDWGRZYKWHYKWJVLYTUVQUULDNWKZUWFUWAUUNYTUULUWGUWKUUNXOUWGYQYSXNUWGX
      MDWLUKULZDWMRZKDWNVNUUNUWLYLYMDWOWPYTUWBUUBUWCKGYTUWBDPLZYLIJZDYKIJZPLZUU
      BYTDUWNYLIYTUWNDYTUULNDWQHZUWNDMUUNXOUWRYQYSXNUWRXMXNDXKEUWRDWRDWSURUKULD
      WTRXAVIYTDSEZUWIUWQUWOMYTDUUNTZYTYKUWJTDYKXBRYTUWPUUAPYTUWSXTSEYDSEUWPUUA
      MUWTYTXTUVATYTYDUVGTDXTYDXCVNVFXDYTKSEUWSUWKUWCKMYTKUWATUWTUWMKDXEVNXFXGX
      HXIXJXJXL $.
      $( [12-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  By subtraction, there is a multiple very close to
       an integer. $)
    irrapxlem3 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 1 ... B ) E. y e.
        NN0 ( abs ` ( ( A x. x ) - y ) ) < ( 1 / B ) ) $=
      ( wcel wa clt wbr co c1 cmin cabs cc0 cle syl syl2anc wceq cr cc recnd va
      vb crp cn cv cmul cmo cfv cdiv cfz wrex cn0 irrapxlem2 cz simplrr elfzelz
      cfl wb simplrl zsubcl a1i simpllr nnz elfz syl3anc ax-1cn subidi ad2antrl
      1z zre ad2antll posdif biimpd imp eqbrtrd zlem1lt mpbird 3syl resubcl 0re
      nnre elfzle1 lesub2 mpbid subid1 elfzle2 mpbir2and adantrr rpre ad3antrrr
      letrd remulcl flcl simpr syl21anc lemul2 syl112anc flwordi subge0 biimpar
      rpgt0 elnn0z sylanbrc subdi oveq1d syl22anc modfrac eqcomd oveq12d 3eqtrd
      ltle sub4 fveq2d 1rp modcl abssub eqtr2d breq1d oveq2 rcla42ev rexlimdvva
      impr ex mpd ) CUCEZDUDEZFZUAUEZUBUEZGHZCYHUFIZJUGIZCYIUFIZJUGIZKILUHZJDUI
      IZGHZFZUBMDUJIZUKUAYSUKCAUEZUFIZBUEZKIZLUHZYPGHZBULUKAJDUJIZUKZUAUBCDUMYG
      YRUUGUAUBYSYSYGYHYSEZYIYSEZFZFZYRUUGUUKYRFYIYHKIZUUFEZYMUQUHZYKUQUHZKIZUL
      EZCUULUFIZUUPKIZLUHZYPGHZUUGUUKYJUUMYQUUKYJFZUUMJUULNHZUULDNHZUVBUULUNEZJ
      UNEZDUNEZUUMUVCUVDFURUVBYIUNEZYHUNEZUVEUVBUUIUVHYGUUHUUIYJUOZYIMDUPZOUVBU
      UHUVIYGUUHUUIYJUSZYHMDUPZOYIYHUTPZUVFUVBVIVAZUVBYFUVGYEYFUUJYJVBZDVCOUULJ
      DVDVEUVBUVCJJKIZUULGHZUVBUVQMUULGUVQMQUVBJVFVGVAUUKYJMUULGHZUUKYJUVSUUKYH
      REZYIREZYJUVSURUUKUVIUVTUUHUVIYGUUIUVMVHYHVJZOUUKUVHUWAUUIUVHYGUUHUVKVKYI
      VJZOYHYIVLPVMVNVOUVBUVFUVEUVCUVRURUVOUVNJUULVPPVQUVBUULYIMKIZDUVBUWAUVTUU
      LREUVBUUIUVHUWAUVJUVKUWCVRZUVBUUHUVIUVTUVLUVMUWBVRZYIYHVSPUVBUWAMREZUWDRE
      UWEUWGUVBVTVAZYIMVSPUVBYFDREUVPDWAOUVBMYHNHZUULUWDNHZUVBUUHUWIUVLYHMDWBOU
      VBUWGUVTUWAUWIUWJURUWHUWFUWEMYHYIWCVEWDUVBUWDYIDNUVBYISEZUWDYIQUVBYIUWETZ
      YIWEOUVBUUIYIDNHUVJYIMDWFOVOWKWGWHUUKYJUUQYQUVBUUPUNEZMUUPNHZUUQUVBUUNUNE
      ZUUOUNEZUWMUVBYMREZUWOUVBCREZUWAUWQYEUWRYFUUJYJCWIWJZUWECYIWLPZYMWMOZUVBY
      KREZUWPUVBUWRUVTUXBUWSUWFCYHWLPZYKWMOZUUNUUOUTPUVBUUNREZUUOREZUUOUUNNHZUW
      NUVBUWOUXEUXAUUNVJOZUVBUWPUXFUXDUUOVJOZUVBUXBUWQYKYMNHZUXGUXCUWTUVBYHYINH
      ZUXJUVBUVTUWAYJUXKUWFUWEUUKYJWNUVTUWAFYJUXKYHYIXKVNWOUVBUVTUWAUWRMCGHZUXK
      UXJURUWFUWEUWSYEUXLYFUUJYJCXAWJYHYICWPWQWDYKYMWRVEUXEUXFFUWNUXGUUNUUOWSWT
      WOUUPXBXCWHUUKYJYQUVAUVBYQUVAUVBYOUUTYPGUVBUUTYNYLKIZLUHZYOUVBUUSUXMLUVBU
      USYMYKKIZUUPKIZYMUUNKIZYKUUOKIZKIZUXMUVBUURUXOUUPKUVBCSEUWKYHSEUURUXOQUVB
      CUWSTUWLUVBYHUWFTCYIYHXDVEXEUVBYMSEYKSEUUNSEUUOSEUXPUXSQUVBYMUWTTUVBYKUXC
      TUVBUUNUXHTUVBUUOUXITYMYKUUNUUOXLXFUVBUXQYNUXRYLKUVBYNUXQUVBUWQYNUXQQUWTY
      MXGOXHUVBYLUXRUVBUXBYLUXRQUXCYKXGOXHXIXJXMUVBYNSEYLSEUXNYOQUVBYNUVBUWQJUC
      EZYNREUWTUXTUVBXNVAZYMJXOPTUVBYLUVBUXBUXTYLREUXCUYAYKJXOPTYNYLXPPXQXRVMYB
      UUEUVAUURUUBKIZLUHZYPGHABUULUUPUUFULYTUULQZUUDUYCYPGUYDUUCUYBLUYDUUAUURUU
      BKYTUULCUFXSXEXMXRUUBUUPQZUYCUUTYPGUYEUYBUUSLUUBUUPUURKXSXMXRXTVEYCYAYD
      $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Eliminate ranges, use positivity of the input to
       force positivity of the output by increasing ` B ` as needed. $)
    irrapxlem4 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. NN E. y e. NN ( abs `
        ( ( A x. x ) - y ) ) < ( 1 / if ( x <_ B , B , x ) ) ) $=
      ( va wcel cn wa co cmin c1 cdiv cle wbr clt cr cc0 syl2anc syl wb vb cmul
      crp cv cabs cfv cfl caddc cif cn0 wrex cfz simpl rpreccl rprege0 flge0nn0
      3syl nn0p1nn ifcl irrapxlem3 simpllr elfznn cz simplr nn0z cneg ad3antrrr
      simpr rpre nnre remulcl nn0re resubcl recn abscl wne nnne0 rereccl 0reALT
      a1i rpne0 flcl zre peano2re max2 nngt0 max1 ltletrd lerec syl22anc flltp1
      cc mpbid wi ltle mpd wceq nncn recrec breqtrrd recgt0 rpgt0 mpbird mulid1
      letrd nnge1 1re lemul2 syl112anc eqbrtrrd subid1 abslt simprd syl3anc jca
      ltsub2 elnnz sylibr redivcl elfzle2 maxle weq oveq2 oveq1d breq1 ifbieq2d
      fveq2d id oveq2d breq12d breq1d rcla42ev ex rexlimdva ) CUCFZDGFZHZCEUDZU
      BIZUAUDZJIZUEUFZKDKCLIZUGUFZKUHIZMNZUUEDUIZLIZONZUAUJUKZEKUUGULIZUKZCAUDZ
      UBIZBUDZJIZUEUFZKUUMDMNZDUUMUIZLIZONZBGUKAGUKZYQYOUUGGFZUULYOYPUMZYQUUEGF
      ZYPUVCYQUUCPFZQUUCMNHZUUDUJFUVEYQYOUUCUCFUVGUVDCUNUUCUOUQUUCUPUUDURUQZYOY
      PVHZUUFUUEDGUSZREUACUUGUTRYQUUJUVBEUUKYQYRUUKFZHZUUIUVBUAUJUVLYTUJFZHZUUI
      UVBUVNUUIHZYRGFZYTGFZUUBKYRDMNZDYRUIZLIZONZUVBUVOUVKUVPYQUVKUVMUUIVAZYRUU
      GVBSZUVOYTVCFZQYTONZHUVQUVOUWDUWEUVOUVMUWDUVLUVMUUIVDZYTVESUVOUWEUUAYSQJI
      ZONZUVOUWGVFUUAONZUWHUVOUUBUWGONZUWIUWHHZUVOUUBUUHUWGUVOUUAWLFZUUBPFUVOUU
      APFZUWLUVOYSPFZYTPFZUWMUVOCPFZYRPFZUWNUVOYOUWPYQYOUVKUVMUUIUVDVGZCVISZUVO
      UVPUWQUWCYRVJSZCYRVKRZUVOUVMUWOUWFYTVLSZYSYTVMRZUUAVNSUUAVOSZUVOUUGPFZUUG
      QVPZUUHPFUVOUVCUXEUVOUVEYPUVCYQUVEUVKUVMUUIUVHVGZYQYPUVKUVMUUIUVIVGZUVJRZ
      UUGVJSZUVOUVCUXFUXIUUGVQSUUGVRRZUVOUWNQPFZUWGPFZUXAUXLUVOVSVTZYSQVMRZUVNU
      UIVHZUVOUUHCUWGUXKUWSUXOUVOUUHKUUELIZCUXKUVOUUEPFZUUEQVPZUXQPFZUVOUUDPFZU
      XRUVOUVFUUDVCFUYAUVOUWPCQVPZUVFUWSUVOYOUYBUWRCWASCVRRZUUCWBUUDWCUQUUDWDSZ
      UVOUVEUXSUXGUUEVQSZUUEVRRZUWSUVOUUEUUGMNZUUHUXQMNZUVODPFZUXRUYGUVOYPUYIUX
      HDVJSZUYDDUUEWERUVOUXRQUUEONZUXEQUUGONZUYGUYHTUYDUVOUVEUYKUXGUUEWFSZUXJUV
      OQDUUGUXNUYJUXJUVOYPQDONUXHDWFSZUVOUYIUXRDUUGMNZUYJUYDDUUEWGRZWHZUUEUUGWI
      WJWMUVOUXQCMNZUUCKUXQLIZMNZUVOUUCUUEUYSMUVOUUCUUEONZUUCUUEMNZUVOUVFVUAUYC
      UUCWKSUVOUVFUXRVUAVUBWNUYCUYDUUCUUEWORWPUVOUUEWLFZUXSUYSUUEWQUVOUVEVUCUXG
      UUEWRSUYEUUEWSRWTUVOUXTQUXQONZUWPQCONZUYRUYTTUYFUVOUXRUYKVUDUYDUYMUUEXARU
      WSUVOYOVUEUWRCXBSZUXQCWIWJXCXEUVOCYSUWGMUVOCKUBIZCYSMUVOCWLFZVUGCWQUVOUWP
      VUHUWSCVNSCXDSUVOKYRMNZVUGYSMNZUVOUVPVUIUWCYRXFSUVOKPFZUWQUWPVUEVUIVUJTVU
      KUVOXGVTZUWTUWSVUFKYRCXHXIWMXJUVOYSWLFZUWGYSWQUVOUWNVUMUXAYSVNSYSXKSWTXEW
      HUVOUWMUXMUWJUWKTUXCUXOUUAUWGXLRWMXMUVOUXLUWOUWNUWEUWHTUXNUXBUXAQYTYSXPXN
      XCXOYTXQXRUVOUUBUUHUVTUXDUXKUVOVUKUVSPFZUVSQVPZUVTPFVULUVOUVSGFZVUNUVOYPU
      VPVUPUXHUWCUVRDYRGUSRZUVSVJSUVOVUPVUOVUQUVSVQSKUVSXSXNUXPUVOUVSUUGMNZUUHU
      VTMNZUVOVURYRUUGMNZUYOHZUVOVUTUYOUVOUVKVUTUWBYRKUUGXTSUYPXOUVOUWQUYIUXEVU
      RVVATUWTUYJUXJYRDUUGYAXNXCUVOVUNQUVSONUXEUYLVURVUSTUVOUYIUWQVUNUYJUWTUVRD
      YRPUSRZUVOQDUVSUXNUYJVVBUYNUVOUWQUYIDUVSMNUWTUYJYRDWERWHUXJUYQUVSUUGWIWJW
      MWHUVAUWAYSUUOJIZUEUFZUVTONABYRYTGGAEYBZUUQVVDUUTUVTOVVEUUPVVCUEVVEUUNYSU
      UOJUUMYRCUBYCYDYGVVEUUSUVSKLVVEUURUVRUUMYRDUUMYRDMYEVVEYHYFYIYJBUAYBZVVDU
      UBUVTOVVFVVCUUAUEUUOYTYSJYCYGYKYLXNYMYNYNWP $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Switching to real intervals and fraction
       syntax. $)
    irrapxlem5 $p |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. QQ ( 0 < x /\ ( abs
        ` ( x - A ) ) < B /\ ( abs ` ( x - A ) ) < ( ( denom ` x ) ^ -u 2 ) ) )
        $=
      ( crp wcel cmul co cabs cfv c1 cdiv cle wbr clt cc0 cr syl syl2anc wceq
      cc va vb wa cv cmin cfl caddc cif cn wrex cdenom c2 cneg w3a cq simpl cn0
      cexp simpr rpreccl rpre rpge0 jca flge0nn0 nn0p1nn irrapxlem4 wne simplrr
      3syl nnq simplrl nnne0 qdivcl syl3anc nnrp rpdivcl rpgt0 nnre nnnn0 absid
      nn0ge0 eqcomd oveq1d recn qre simplll resubcl absmul subdi divcan2 mulcom
      rpcn oveq12d eqtrd fveq2d remulcl abssub 3eqtrd abscl simpllr ifcl gt0ne0
      qcn rereccl flltp1 ltle syl21anc max2 letrd wb lerec syl22anc mpbid recnd
      imp rpne0 recrec mulid2 eqtr4d nnge1 1re lemul1 syl112anc eqbrtrd ltletrd
      a1i nngt0 ltmul2 mpbird msqgt0 qdencl max1 divdiv1 syl122anc divrec divid
      3eqtr3d breqtrrd cz nnz divdenle le2msq nncn 2nn0 expneg sqval 3jca breq2
      oveq2d oveq1 breq1d fveq2 breq12d 3anbi123d rcla4ev ex rexlimdvva mpd ) B
      DEZCDEZUCZBUAUDZFGZUBUDZUEGZHIZJUVBJCKGZUFIZJUGGZLMZUVIUVBUHZKGZNMZUBUIUJ
      UAUIUJZOAUDZNMZUVOBUEGZHIZCNMZUVRUVOUKIZULUMZURGZNMZUNZAUOUJZUVAUUSUVIUIE
      ZUVNUUSUUTUPUVAUVGPEZOUVGLMZUCUVHUQEZUWFUVAUWGUWHUVAUVGDEZUWGUVAUUTUWJUUS
      UUTUSCUTZQZUVGVAZQUVAUWJUWHUWLUVGVBZQVCUVGVDZUVHVEZVIUAUBBUVIVFRUVAUVMUWE
      UAUBUIUIUVAUVBUIEZUVDUIEZUCZUCZUVMUWEUWTUVMUCZUVDUVBKGZUOEZOUXBNMZUXBBUEG
      ZHIZCNMZUXFUXBUKIZUWAURGZNMZUNZUWEUXAUVDUOEZUVBUOEZUVBOVGZUXCUXAUWRUXLUVA
      UWQUWRUVMVHZUVDVJQUXAUWQUXMUVAUWQUWRUVMVKZUVBVJQUXAUWQUXNUXPUVBVLQZUVDUVB
      VMVNZUXAUXDUXGUXJUXAUXBDEZUXDUXAUVDDEZUVBDEZUXSUXAUWRUXTUXOUVDVOQUXAUWQUY
      AUXPUVBVOQZUVDUVBVPRUXBVQQUXAUXGUVBUXFFGZUVBCFGZNMZUXAUYCUVFUYDNUXAUYCUVB
      HIZUXFFGZUVBUXEFGZHIZUVFUXAUVBUYFUXFFUXAUYFUVBUXAUVBPEZOUVBLMZUYFUVBSUXAU
      WQUYJUXPUVBVRQZUXAUWQUVBUQEUYKUXPUVBVSUVBWAVIZUVBVTRWBWCUXAUYIUYGUXAUVBTE
      ZUXETEZUYIUYGSUXAUYJUYNUYLUVBWDQZUXAUXEPEZUYOUXAUXBPEZBPEZUYQUXAUXCUYRUXR
      UXBWEQUXAUUSUYSUUSUUTUWSUVMWFZBVAQZUXBBWGRZUXEWDZQUVBUXEWHRWBUXAUYIUVDUVC
      UEGZHIZUVFUXAUYHVUDHUXAUYHUVBUXBFGZUVBBFGZUEGZVUDUXAUYNUXBTEZBTEZUYHVUHSU
      YPUXAUXCVUIUXRUXBXCQUXAUUSVUJUYTBWLQZUVBUXBBWIVNUXAVUFUVDVUGUVCUEUXAUVDTE
      ZUYNUXNVUFUVDSUXAUVDPEZVULUXAUWRVUMUXOUVDVRQZUVDWDQZUYPUXQUVDUVBWJVNUXAUY
      NVUJVUGUVCSUYPVUKUVBBWKRWMWNWOUXAVULUVCTEZVUEUVFSVUOUXAUVCPEZVUPUXAUYSUYJ
      VUQVUAUYLBUVBWPRZUVCWDQUVDUVCWQRWNWRZUXAUVFUVLUYDUXAUVEPEZUVETEUVFPEUXAVU
      QVUMVUTVURVUNUVCUVDWGRUVEWDUVEWSVIZUXAUVKPEZUVKOVGZUVLPEUXAUVIPEZUYJVVBUX
      AUWFVVDUXAUWIUWFUXAUWGUWHUWIUXAUWJUWGUXAUUTUWJUUSUUTUWSUVMWTZUWKQZUWMQZUX
      AUWJUWHVVFUWNQUWORUWPQZUVIVRQZUYLUVJUVIUVBPXARZUXAVVBOUVKNMZVVCVVJUXAUVKD
      EZVVKUXAUVIDEZUYAVVLUXAUWFVVMVVHUVIVOQUYBUVJUVIUVBDXARUVKVQQZUVKXBRUVKXDR
      ZUXAUYJCPEZUYDPEUYLUXAUUTVVPVVECVAQZUVBCWPRZUWTUVMUSZUXAUVLJUVGKGZUYDVVOU
      XAUWJVVTDEVVTPEVVFUVGUTVVTVAVIVVRUXAUVGUVKLMZUVLVVTLMZUXAUVGUVIUVKVVGVVIV
      VJUXAUWGVVDUVGUVINMZUVGUVILMZVVGVVIUXAUWGVWCVVGUVGXEQUWGVVDUCVWCVWDUVGUVI
      XFXOXGUXAUYJVVDUVIUVKLMUYLVVIUVBUVIXHRXIUXAUWGOUVGNMZVVBVVKVWAVWBXJVVGUXA
      UWJVWEVVFUVGVQQVVJVVNUVGUVKXKXLXMUXAVVTJCFGZUYDLUXAVVTCVWFUXACTEZCOVGZVVT
      CSUXACVVQXNZUXAUUTVWHVVECXPQCXQRUXAVWGVWFCSVWICXRQXSUXAJUVBLMZVWFUYDLMZUX
      AUWQVWJUXPUVBXTQUXAJPEZUYJVVPOCNMZVWJVWKXJVWLUXAYAYFUYLVVQUXAUUTVWMVVECVQ
      QJUVBCYBYCXMYDXIYEYDUXAUXFPEZVVPUYJOUVBNMZUXGUYEXJUXAUYQUYOVWNVUBVUCUXEWS
      VIZVVQUYLUXAUWQVWOUXPUVBYGQZUXFCUVBYHYCYIUXAUXFJUXHUXHFGZKGZUXINUXAUXFJUV
      BUVBFGZKGZVWSVWPUXAVWTPEZVWTOVGZVXAPEZUXAUYJUYJVXBUYLUYLUVBUVBWPRZUXAVXBO
      VWTNMZVXCVXEUXAUYJUXNVXFUYLUXQUVBYJRZVWTXBRZVWTXDRZUXAVWRPEZVWROVGZVWSPEU
      XAUXHPEZVXLVXJUXAUXHUIEZVXLUXAUXCVXMUXRUXBYKQZUXHVRQZVXOUXHUXHWPRZUXAVXJO
      VWRNMZVXKVXPUXAVXLUXHOVGZVXQVXOUXAVXMVXRVXNUXHVLQUXHYJRZVWRXBRVWRXDRUXAUX
      FVXANMZUYCUVBVXAFGZNMZUXAUYCUVFVYANVUSUXAUVFJUVBKGZVYANUXAUVFUVLVYCVVAVVO
      UXAUYJUXNVYCPEUYLUXQUVBXDRVVSUXAUVBUVKLMZUVLVYCLMZUXAUYJVVDVYDUYLVVIUVBUV
      IYLRUXAUYJVWOVVBVVKVYDVYEXJUYLVWQVVJVVNUVBUVKXKXLXMYEUXAUVBVWTKGZUVBUVBKG
      ZUVBKGZVYAVYCUXAVYHVYFUXAUYNUYNUXNUYNUXNVYHVYFSUYPUYPUXQUYPUXQUVBUVBUVBYM
      YNWBUXAUYNVWTTEZVXCVYFVYASUYPUXAVXBVYIVXEVWTWDQVXHUVBVWTYOVNUXAVYGJUVBKUX
      AUYNUXNVYGJSUYPUXQUVBYPRWCYQYRYDUXAVWNVXDUYJVWOVXTVYBXJVWPVXIUYLVWQUXFVXA
      UVBYHYCYIUXAVWRVWTLMZVXAVWSLMZUXAUXHUVBLMZVYJUXAUVDYSEZUWQVYLUXAUWRVYMUXO
      UVDYTQUXPUVDUVBUUARUXAVXLOUXHLMZUYJUYKVYLVYJXJVXOUXAVXMUXHUQEVYNVXNUXHVSU
      XHWAVIUYLUYMUXHUVBUUBXLXMUXAVXJVXQVXBVXFVYJVYKXJVXPVXSVXEVXGVWRVWTXKXLXMY
      EUXAUXIJUXHULURGZKGZVWSUXAUXHTEZULUQEZUXIVYPSUXAVXMVYQVXNUXHUUCQZVYRUXAUU
      DYFUXHULUUERUXAVYOVWRJKUXAVYQVYOVWRSVYSUXHUUFQUUIWNYRUUGUWDUXKAUXBUOUVOUX
      BSZUVPUXDUVSUXGUWCUXJUVOUXBONUUHVYTUVRUXFCNVYTUVQUXEHUVOUXBBUEUUJWOZUUKVY
      TUVRUXFUWBUXINWUAVYTUVTUXHUWAURUVOUXBUKUULWCUUMUUNUUORUUPUUQUUR $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Explicit description of a non-closed set. $)
    irrapxlem6 $p |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. { y e. QQ | ( 0 < y
        /\ ( abs ` ( y - A ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ( abs ` ( x - A )
        ) < B ) $=
      ( va crp wcel wa cc0 cv clt wbr cmin co cabs cfv cdenom cexp cq wrex cneg
      w3a crab irrapxlem5 simplr simpr1 simpr3 jca weq breq2 oveq1 fveq2d fveq2
      c2 oveq1d breq12d anbi12d elrab sylibr simpr2 breq1d rcla4ev ex rexlimdva
      syl2anc mpd ) CFGDFGHZIEJZKLZVHCMNZOPZDKLZVKVHQPZUNUAZRNZKLZUBZESTAJZCMNZ
      OPZDKLZAIBJZKLZWBCMNZOPZWBQPZVNRNZKLZHZBSUCZTZECDUDVGVQWKESVGVHSGZHZVQWKW
      MVQHZVHWJGZVLWKWNWLVIVPHZHWOWNWLWPVGWLVQUEWNVIVPWMVIVLVPUFWMVIVLVPUGUHUHW
      IWPBVHSBEUIZWCVIWHVPWBVHIKUJWQWEVKWGVOKWQWDVJOWBVHCMUKULWQWFVMVNRWBVHQUMU
      OUPUQURUSWMVIVLVPUTWAVLAVHWJAEUIZVTVKDKWRVSVJOVRVHCMUKULVAVBVEVCVDVF $.
      $( [13-Sep-2014] $)

    $( Lagrange's rational approximation theorem.  Every positive irrational
       number has infinitely many rational approximations which are closer than
       the inverse squares of their reduced denominators.  Lemma 62 in
       [vandenDries]. $)
    irrapx1 $p |- ( A e. ( RR+ \ QQ ) -> { y e. QQ | ( 0 < y /\ ( abs ` ( y - A
        ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ~~ NN ) $=
      ( vb va crp cq wcel com cen wbr cn wa cv clt cmin co cabs cfv wss cr cdif
      cc0 cdenom c2 cneg cexp crab cfn wn qnnen nnenom entri pm3.2i wrex ssrab2
      wral qssre sstri eldifi rpre eldifn sseli nsyl irrapxlem6 sylan ralrimiva
      a1i syl rencldnfi syl31anc jctil ctbnfien sylancr ) BEFUAGZFHIJZKHIJZLUBA
      MZNJVQBOPQRVQUCRUDUEUFPNJLZAFUGZFSZVSUHGUIZLVSKIJVOVPFKHUJUKULUKUMVNWAVTV
      NVSTSZBTGZBVSGZUICMBOPQRDMZNJCVSUNZDEUPWAWBVNVSFTVRAFUOZUQURVGVNBEGZWCBEF
      USZBUTVHVNBFGWDBEFVAVSFBWGVBVCVNWFDEVNWHWEEGWFWICABWEVDVEVFDCVSBVIVJWGVKV
      SFKVLVM $.
      $( [14-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Pell equations 1: A nontrivial solution always exists
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( the following development comprises [vandenDries] lemma 62, credited to Dirichlet $)
  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $( a bit of terminology - Pell field = Q[sqr d], Pell ring = Z[sqr d] (algebraic integers in Pell field), Pell group = right branch of the group of units in Pell ring - isomorphic to ZZ, Pell semigroup = Pell group elements >= 1, resembles NN0 $)

    $( Lemma for ~ pellex .  Arithmetical core of pellexlem3, norm lower
       bound. $)
    pellexlem1 $p |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ -. ( sqr ` D ) e.
        QQ ) -> ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) =/= 0 ) $=
      ( cn wcel csqr cfv cq c2 cexp co cc0 wne wceq cc wb 3ad2ant2 syl 3ad2ant3
      nncn w3a wn cmul cmin sqcl 3ad2ant1 mulcl syl2anc subeq0 cdiv nnne0 sqne0
      mpbird divmul3 syl112anc sqdiv fveq2d syl3anc cr cle wbr nnre redivcl clt
      cn0 nnnn0 nn0ge0 nngt0 divge0 syl22anc sqrsq eqtr3d qdivcl eqeltrd eleq1d
      nnq fveq2 syl5ibcom sylbird sylbid necon3bd imp ) CDEZADEZBDEZUAZCFGZHEZU
      BAIJKZCBIJKZUCKZUDKZLMWFWHWLLWFWLLNZWIWKNZWHWFWIOEZWKOEZWMWNPWFAOEZWOWDWC
      WQWEATQZAUERZWFCOEZWJOEZWPWCWDWTWECTUFZWFBOEZXAWEWCXCWDBTSZBUERZCWJUGUHWI
      WKUIUHWFWNWIWJUJKZCNZWHWFWOWTXAWJLMZXGWNPWSXBXEWFXHBLMZWEWCXIWDBUKSZWFXCX
      HXIPXDBULRUMWICWJUNUOWFXFFGZHEXGWHWFXKABUJKZHWFXLIJKZFGZXKXLWFWQXCXIXNXKN
      WRXDXJWQXCXIUAXMXFFABUPUQURWFXLUSEZLXLUTVAZXNXLNWFAUSEZBUSEZXIXOWDWCXQWEA
      VBQZWEWCXRWDBVBSZXJABVCURWFXQLAUTVAZXRLBVDVAZXPXSWDWCYAWEWDAVEEYAAVFAVGRQ
      XTWEWCYBWDBVHSABVIVJXLVKUHVLWFAHEZBHEZXIXLHEWDWCYCWEAVPQWEWCYDWDBVPSXJABV
      MURVNXGXKWGHXFCFVQVOVRVSVTWAWB $.
      $( [14-Sep-2014] $)

    $( Lemma for ~ pellex .  Arithmetical core of pellexlem3, norm upper
       bound. $)
    pellexlem2 $p |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ ( abs ` ( ( A / B
        ) - ( sqr ` D ) ) ) < ( B ^ -u 2 ) ) -> ( abs ` ( ( A ^ 2 ) - ( D x. (
        B ^ 2 ) ) ) ) < ( 1 + ( 2 x. ( sqr ` D ) ) ) ) $=
      ( wcel co cabs c2 clt wbr cmul caddc c1 cc cc0 cr syl syl2anc syl3anc cle
      wceq cn w3a cdiv csqr cfv cmin cneg cexp wa wne simpl2 nncn simpl1 simpl3
      sqcl mulcl subcl abscl recn nnne0 sqne0 biimprd imp divcan2 eqcomd resqcl
      nnre sqge0 absid oveq2d eqtrd divsubdir syl112anc sqdiv divcan4 cn0 nnnn0
      absdiv nn0ge0 resqrcl sqval remsqsqr eqtr2d oveq12d divcl redivcl resubcl
      subsq addcl mulcom 3eqtrd fveq2d absmul remulcl cz 2nn0 nn0negzi reexpclz
      a1i 1re 2re readdcl simpr wb nngt0 divgt0 syl22anc sqrgt0 addgt0 syl21anc
      gt0ne0 absgt0 biimpd ltmul1 mpbid sqgt0 ltmul2 expclz mulass expneg recid
      jca oveq1d mulid2 addcom ppncan 2times abstri nn0ge0i sqrge0 mulge0 nnge1
      3syl nnsqcl lt01 lerec ax-1cn div1i eqbrtrd ltletrd breqtrd leadd1 letrd
      ltle ) CUADZAUADZBUADZUBZABUCEZCUDUEZUFEZFUEZBGUGZUHEZHIZUIZAGUHEZCBGUHEZ
      JEZUFEZFUEZUURUUKUUIUUJKEZJEZFUEZJEZLGUUJJEZKEZHUUPUVAUURUUTUURUCEZFUEZJE
      ZUVEUUPUVAUURUVAUURUCEZJEZUVJUUPUVLUVAUUPUVAMDZUURMDZUURNUJZUVLUVATUUPUVA
      ODZUVMUUPUUTMDZUVPUUPUUQMDZUUSMDZUVQUUPAMDZUVRUUPUUFUVTUUEUUFUUGUUOUKZAUL
      PZAUOPZUUPCMDZUVNUVSUUPUUEUWDUUEUUFUUGUUOUMZCULPZUUPBMDZUVNUUPUUGUWGUUEUU
      FUUGUUOUNZBULPZBUOPZCUURUPQZUUQUUSUQQZUUTURPUVAUSPUWJUUPUWGBNUJZUVOUWIUUP
      UUGUWMUWHBUTPZUWGUWMUVOUWGUVOUWMBVAVBVCQZUVAUURVDRVEUUPUVKUVIUURJUUPUVKUV
      AUURFUEZUCEZUVIUUPUURUWPUVAUCUUPUWPUURUUPUURODZNUURSIZUWPUURTUUPBODZUWRUU
      PUUGUWTUWHBVGPZBVFPZUUPUWTUWSUXABVHPUURVIQVEVJUUPUVIUWQUUPUVQUVNUVOUVIUWQ
      TUWLUWJUWOUUTUURVRRVEVKVJVKUUPUVIUVDUURJUUPUVHUVCFUUPUVHUUQUURUCEZUUSUURU
      CEZUFEZUUIGUHEZUUJGUHEZUFEZUVCUUPUVRUVSUVNUVOUVHUXETUWCUWKUWJUWOUUQUUSUUR
      VLVMUUPUXCUXFUXDUXGUFUUPUXFUXCUUPUVTUWGUWMUXFUXCTUWBUWIUWNABVNRVEUUPUXDCU
      XGUUPUWDUVNUVOUXDCTUWFUWJUWOCUURVORUUPUXGUUJUUJJEZCUUPUUJMDZUXGUXITUUPUUJ
      ODZUXJUUPCODZNCSIZUXKUUPUUEUXLUWECVGPZUUPCVPDZUXMUUPUUEUXOUWECVQPCVSPZCVT
      QZUUJUSPZUUJWAPUUPUXLUXMUXICTUXNUXPCWBQWCVKWDUUPUXHUVBUUKJEZUVCUUPUUIMDZU
      XJUXHUXSTUUPUVTUWGUWMUXTUWBUWIUWNABWERZUXRUUIUUJWHQUUPUVBMDZUUKMDZUXSUVCT
      UUPUXTUXJUYBUYAUXRUUIUUJWIQZUUPUUKODZUYCUUPUUIODZUXKUYEUUPAODZUWTUWMUYFUU
      PUUFUYGUWAAVGPZUXAUWNABWFRZUXQUUIUUJWGQZUUKUSPZUVBUUKWJQVKWKWLVJVKUUPUVEU
      URUULUVBFUEZJEZJEZUVGHUUPUVDUYMUURJUUPUYCUYBUVDUYMTUYKUYDUUKUVBWMQVJUUPUY
      NUURUUNUYLJEZJEZUVGUUPUWRUYMODZUYNODUXBUUPUULODZUYLODZUYQUUPUYCUYRUYKUUKU
      RPZUUPUYBUYSUYDUVBURPZUULUYLWNQZUURUYMWNQUUPUWRUYOODZUYPODUXBUUPUUNODZUYS
      VUCUUPUWTUWMUUMWODZVUDUXAUWNVUEUUPGWPWQWSZBUUMWRRZVUAUUNUYLWNQZUURUYOWNQU
      UPLODZUVFODZUVGODVUIUUPWTWSZUUPGODZUXKVUJVULUUPXAWSZUXQGUUJWNQZLUVFXBQZUU
      PUYMUYOHIZUYNUYPHIZUUPUUOVUPUUHUUOXCZUUPUYRVUDUYSNUYLHIZUUOVUPXDUYTVUGVUA
      UUPUYBUVBNUJZVUSUYDUUPUVBODZNUVBHIZVUTUUPUYFUXKVVAUYIUXQUUIUUJXBQUUPUYFUX
      KNUUIHIZNUUJHIZUIVVBUYIUXQUUPVVCVVDUUPUYGNAHIZUWTNBHIZVVCUYHUUPUUFVVEUWAA
      XEPUXAUUPUUGVVFUWHBXEPABXFXGUUPUXLNCHIZVVDUXNUUPUUEVVGUWECXEPCXHQYBUUIUUJ
      XIXJUVBXKQUYBVUTVUSUYBVUTVUSUVBXLXMVCQUULUUNUYLXNVMXOUUPUYQVUCUWRNUURHIZV
      UPVUQXDVUBVUHUXBUUPUWTUWMVVHUXAUWNBXPQZUYMUYOUURXQVMXOUUPUYPUYLUVGSUUPUYP
      UURUUNJEZUYLJEZLUYLJEZUYLUUPUVNUUNMDZUYLMDZUYPVVKTUWJUUPUWGUWMVUEVVMUWIUW
      NVUFBUUMXRRUUPUYSVVNVUAUYLUSPZUVNVVMVVNUBVVKUYPUURUUNUYLXSVERUUPVVJLUYLJU
      UPVVJUURLUURUCEZJEZLUUPUUNVVPUURJUUPUWGGVPDZUUNVVPTUWIVVRUUPWPWSBGXTQZVJU
      UPUVNUVOVVQLTUWJUWOUURYAQVKYCUUPVVNVVLUYLTVVOUYLYDPWKUUPUYLUUKUVFKEZFUEZU
      VGSUUPUVBVVTFUUPUVBUUJUUIKEZUUJUUJKEZUUKKEZVVTUUPUXTUXJUVBVWBTUYAUXRUUIUU
      JYEQUUPUXJUXJUXTVWBVWDTUXRUXRUYAUXJUXJUXTUBVWDVWBUUJUUJUUIYFVERUUPVWDUUKV
      WCKEZVVTUUPVWCMDZUYCVWDVWETUUPUXJUXJVWFUXRUXRUUJUUJWIQUYKVWCUUKYEQUUPVWCU
      VFUUKKUUPUXJVWCUVFTUXRUXJUVFVWCUUJYGVEPVJVKWKWLUUPVWAUULUVFFUEZKEZUVGUUPV
      VTODZVVTMDVWAODUUPUYEVUJVWIUYJVUNUUKUVFXBQVVTUSVVTURYMUUPUYRVWGODZVWHODUY
      TUUPUVFMDZVWJUUPVUJVWKVUNUVFUSPZUVFURPUULVWGXBQVUOUUPUYCVWKVWAVWHSIUYKVWL
      UUKUVFYHQUUPVWHUULUVFKEZUVGSUUPVWGUVFUULKUUPVUJNUVFSIZVWGUVFTVUNUUPVULNGS
      IZUXKNUUJSIZVWNVUMVWOUUPGWPYIWSUXQUUPUXLUXMVWPUXNUXPCYJQGUUJYKXGUVFVIQVJU
      UPUULLSIZVWMUVGSIZUUPUYRVUIUULLHIZVWQUYTVUKUUPUULUUNLUYTVUGVUKVURUUPUUNVV
      PLSVVSUUPVVPLLUCEZLSUUPLUURSIZVVPVWTSIZUUPUURUADZVXAUUPUUGVXCUWHBYNPUURYL
      PUUPVUINLHIZUWRVVHVXAVXBXDVUKVXDUUPYOWSUXBVVILUURYPXGXOVWTLTUUPLYQYRWSUUA
      YSYTUYRVUIUIVWSVWQUULLUUDVCXJUUPUYRVUIVUJVWQVWRXDUYTVUKVUNUULLUVFUUBRXOYS
      UUCYSYSYTYSYS $.
      $( [14-Sep-2014] $)

    ${
      $d D x y z $.
      $( Lemma for ~ pellex .  To each good rational approximation of
         ` ( sqr `` D ) ` , there exists a near-solution. $)
      pellexlem3 $p |- ( ( D e. NN /\ -. ( sqr ` D ) e. QQ ) -> { x e. QQ | ( 0
          < x /\ ( abs ` ( x - ( sqr ` D ) ) ) < ( ( denom ` x ) ^ -u 2 ) ) }
          ~<_ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D
          x. ( z ^ 2 ) ) ) =/= 0 /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) )
          ) < ( 1 + ( 2 x. ( sqr ` D ) ) ) ) ) } ) $=
        ( cn wcel cfv cq wa cc0 cv clt wbr cmin co cabs cdenom c2 cexp wceq cvv
        va vb csqr wn cneg crab cmul wne c1 caddc copab qex ssrab2 ssexi cnumer
        cdom cop simprl simprrl syl2anc qdencl syl jca simpll simplr pellexlem1
        qgt0numnn syl31anc cdiv simprrr qeqnumdivden oveq1d fveq2d breq1d mpbid
        wb pellexlem2 ex weq breq2 oveq1 fveq2 breq12d anbi12d elrab fvex eleq1
        anbi1d neeq1d anbi2d oveq2d opelopab 3imtr4g sseldi simprr opth oveq12d
        3eqtr4d syl5bi opeq12d impbid1 dom2d mpi ) DEFZDUDGZHFUEZIZJAKZLMZXIXFN
        OZPGZXIQGZRUFZSOZLMZIZAHUGZUAFXRBKZEFZCKZEFZIZXSRSOZDYARSOZUHOZNOZJUIZY
        GPGZUJRXFUHOUKOZLMZIZIZBCULZUQMXRHUMXQAHUNZUOXHUBUCXRYNUBKZUPGZYPQGZURZ
        UCKZUPGZYTQGZURZUAXHYPHFZJYPLMZYPXFNOZPGZYRXNSOZLMZIZIZYQEFZYREFZIZYQRS
        OZDYRRSOZUHOZNOZJUIZUURPGZYJLMZIZIZYPXRFZYSYNFXHUUKUVCXHUUKIZUUNUVBUVEU
        ULUUMUVEUUDUUEUULXHUUDUUJUSZXHUUDUUEUUIUTYPVHVAZUVEUUDUUMUVFYPVBVCZVDUV
        EUUSUVAUVEXEUULUUMXGUUSXEXGUUKVEZUVGUVHXEXGUUKVFYQYRDVGVIUVEXEUULUUMYQY
        RVJOZXFNOZPGZUUHLMZUVAUVIUVGUVHUVEUUIUVMXHUUDUUEUUIVKUVEUUDUUIUVMVQUVFU
        UDUUGUVLUUHLUUDUUFUVKPUUDYPUVJXFNYPVLZVMVNVOVCVPYQYRDVRVIVDVDVSXQUUJAYP
        HAUBVTZXJUUEXPUUIXIYPJLWAUVOXLUUGXOUUHLUVOXKUUFPXIYPXFNWBVNUVOXMYRXNSXI
        YPQWCVMWDWEWFYMUULYBIZUUOYFNOZJUIZUVQPGZYJLMZIZIUVCBCYQYRYPUPWGZYPQWGZX
        SYQTZYCUVPYLUWAUWDXTUULYBXSYQEWHWIUWDYHUVRYKUVTUWDYGUVQJUWDYDUUOYFNXSYQ
        RSWBVMZWJUWDYIUVSYJLUWDYGUVQPUWEVNVOWEWEYAYRTZUVPUUNUWAUVBUWFYBUUMUULYA
        YREWHWKUWFUVRUUSUVTUVAUWFUVQUURJUWFYFUUQUUONUWFYEUUPDUHYAYRRSWBWLWLZWJU
        WFUVSUUTYJLUWFUVQUURPUWGVNVOWEWEWMWNXHUVDYTXRFZIZYSUUCTZUBUCVTZVQZXHUWI
        IZUUDYTHFZUWLUWMXRHYPYOXHUVDUWHUSWOUWMXRHYTYOXHUVDUWHWPWOUUDUWNIZUWJUWK
        UWJYQUUATZYRUUBTZIZUWOUWKYQYRUUAUUBUWBUWCYTQWGWQUWOUWRUWKUWOUWRIZUVJUUA
        UUBVJOZYPYTUWSYQUUAYRUUBVJUWOUWPUWQUSUWOUWPUWQWPWRUWSUUDYPUVJTUUDUWNUWR
        VEUVNVCUWSUWNYTUWTTUUDUWNUWRVFYTVLVCWSVSWTUWKYQUUAYRUUBYPYTUPWCYPYTQWCX
        AXBVAVSXCXD $.
        $( [14-Sep-2014] $)
    $}

    ${
      $d D y z $.
      $( Lemma for ~ pellex .  Invoking ~ irrapx1 , we have infinitely many
         near-solutions. $)
      pellexlem4 $p |- ( ( D e. NN /\ -. ( sqr ` D ) e. QQ ) -> { <. y , z >. |
          ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) =/=
          0 /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) ) < ( 1 + ( 2 x. (
          sqr ` D ) ) ) ) ) } ~~ NN ) $=
        ( vb cn wcel cfv cq wa cv c2 cexp co cmul clt wbr cdom cen nnex crp cc0
        csqr wn cmin wne cabs c1 caddc copab cxp cvv xpex opabssxp ssexi ssdomg
        wss mp2 xpnnen domentr mp2an a1i cdenom cneg crab cdif nnrp rpsqrcl syl
        anim1i eldif sylibr irrapx1 ensym 3syl pellexlem3 endomtr syl2anc sbth
        ) CEFZCUBGZHFUCZIZAJZEFBJZEFIWCKLMCWDKLMNMUDMZUAUEWEUFGUGKVTNMUHMOPIZIA
        BUIZEQPZEWGQPZWGERPWHWBWGEEUJZQPZWJERPWHWGUKFWGWJUPWKWGWJEESSULWFABEEUM
        ZUNWLWGWJUKUOUQURWGWJEUSUTVAWBEUADJZOPWMVTUDMUFGWMVBGKVCLMOPIDHVDZRPZWN
        WGQPWIWBVTTHVEFZWNERPWOWBVTTFZWAIWPVSWQWAVSCTFWQCVFCVGVHVIVTTHVJVKDVTVL
        WNESVMVNDABCVOEWNWGVPVQWGEVRVQ $.
        $( [14-Sep-2014] $)
    $}

    $( we're not defining the Pell-field, Pell-ring, and Pell-norm explicitly because after this construction is done we will never use them $)
    $( TODO: redo this with general algebraic number theory once that is available in set.mm $)

    ${
      $d D x y z $.
      $( Lemma for ~ pellex .  Invoking ~ fiphpd3 , we have infinitely many
         near-solutions for some specific norm. $)
      pellexlem5 $p |- ( ( D e. NN /\ -. ( sqr ` D ) e. QQ ) -> E. x e. ZZ ( x
          =/= 0 /\ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( y ^ 2 ) - (
          D x. ( z ^ 2 ) ) ) = x ) } ~~ NN ) ) $=
        ( va cn wcel cfv wa c2 cexp co cmul cmin wceq cc0 wbr cz syl cr vb csqr
        cq wn cv c1st c2nd wne cabs c1 caddc clt crab cen cfl cneg cfz csn cdif
        copab wrex pellexlem4 cfn fzfi diffi ax-mp a1i cop elopab oveq1d oveq2d
        wex fveq2 oveq12d vex op1st oveq1i op2nd oveq2i oveq12i syl6eq ad2antrl
        simprrl simpl simprr ad2antll cle ad2antrr simplr zmulcl syl2anc zsubcl
        nnz zsqcl 1re 2re nnre cn0 nnnn0 nn0ge0 resqrcl remulcl sylancr readdcl
        flcl znegcl zre nn0abscl nn0z 3syl peano2re flltp1 lttrd zleltp1 mpbird
        absle biimpa syl21anc w3a elfz biimpar syl31anc syl12anc adantlr simprl
        wb ex syl5bi wi 3ad2ant3 3exp imp3a cdom cvv nnex opabssxp ssexi ssdomg
        wss jca32 eldifsn sylanbrc eqeltrd exlimdvv imp weq eldif elfzelz simp2
        fiphp3dOLD elsn biimpri necon3bi jca syl5 simp2l simp2r cxp xpex xpnnen
        domentr mp2an ensym rabex elrab syl6req 2eximdv 3imtr4g expimpd ancomsd
        mp2 eqeq1d eqtrd ssrdv 3adant3 mpsyl endomtr sbth syld reximdv2 mpd ) D
        FGZDUBHZUCGUDZIZEUEZUFHZJKLZDUWFUGHZJKLZMLZNLZAUEZOZEBUEZFGZCUEZFGZIZUW
        OJKLZDUWQJKLZMLZNLZPUHZUXCUIHZUJJUWCMLZUKLZULQZIZIZBCUTZUMZFUNQZAUXGUOH
        ZUPZUXNUQLZPURZUSZVAUWMPUHZUWSUXCUWMOZIZBCUTZFUNQZIZARVAUWEEAUAUXKUXRUW
        LUAUEZUFHZJKLZDUYEUGHZJKLZMLZNLZBCDVBUXRVCGZUWEUXPVCGUYLUXOUXNVDUXPUXQV
        EVFVGUWEUWFUXKGZUWLUXRGZUYMUWFUWOUWQVHZOZUXJIZCVLBVLUWEUYNUXJBCUWFVIUWE
        UYQUYNBCUWEUYQUYNUWEUYQIZUWLUXCUXRUYPUWLUXCOUWEUXJUYPUWLUYOUFHZJKLZDUYO
        UGHZJKLZMLZNLZUXCUYPUWHUYTUWKVUCNUYPUWGUYSJKUWFUYOUFVMVJUYPUWJVUBDMUYPU
        WIVUAJKUWFUYOUGVMVJVKVNUYTUWTVUCUXBNUYSUWOJKUWOUWQBVOZVPVQVUBUXADMVUAUW
        QJKUWOUWQVUECVOVRVQVSVTZWAWBUYRUXCUXPGZUXDUXCUXRGUWBUYQVUGUWDUWBUYQIUWS
        UWBUXHVUGUWBUYPUWSUXIWCUWBUYQWDUXJUXHUWBUYPUWSUXDUXHWEWFUWSUWBUXHIZIZUX
        CRGZUXORGZUXNRGZUXOUXCWGQUXCUXNWGQIZVUGVUIUWTRGZUXBRGZVUJVUIUWORGZVUNUW
        PVUPUWRVUHUWOWMWHUWOWNSVUIDRGZUXARGZVUOUWBVUQUWSUXHDWMWBVUIUWQRGZVURVUI
        UWRVUSUWPUWRVUHWIUWQWMSUWQWNSDUXAWJWKUWTUXBWLWKZVUIVULVUKVUIUXGTGZVULVU
        IUJTGUXFTGZVVAWOVUIJTGUWCTGZVVBWPVUIDTGZPDWGQZVVCUWBVVDUWSUXHDWQWBVUIDW
        RGZVVEUWBVVFUWSUXHDWSWBDWTSDXAWKJUWCXBXCUJUXFXDXCZUXGXESZUXNXFSVVHVUIUX
        CTGZUXNTGZUXEUXNWGQZVUMVUIVUJVVIVUTUXCXGSVUIVULVVJVVHUXNXGSZVUIVVKUXEUX
        NUJUKLZULQZVUIUXEUXGVVMVUIUXERGZUXETGVUIVUJUXEWRGVVOVUTUXCXHUXEXIXJZUXE
        XGSVVGVUIVVJVVMTGVVLUXNXKSUWSUWBUXHWEVUIVVAUXGVVMULQVVGUXGXLSXMVUIVVOVU
        LVVKVVNYFVVPVVHUXEUXNXNWKXOVVIVVJIVVKVUMUXCUXNXPXQXRVUJVUKVULXSVUGVUMUX
        CUXOUXNXTYAYBYCYDUXJUXDUWEUYPUWSUXDUXHYEWFUXCUXPPUUAUUBUUCYGUUDYHUUEEUA
        UUFZUWHUYGUWKUYJNVVQUWGUYFJKUWFUYEUFVMVJVVQUWJUYIDMVVQUWIUYHJKUWFUYEUGV
        MVJVKVNZUUJUWEUXMUYDAUXRRUWEUWMUXRGZUXMUWMRGZUYDIZUWEVVSVVTUXSIZUXMVWAY
        IVVSUWMUXPGZUWMUXQGZUDZIUWEVWBUWMUXPUXQUUGUWEVWCVWEVWBVWCVVTUWEVWEVWBYI
        UWMUXOUXNUUHUWEVVTVWEVWBUWEVVTVWEXSVVTUXSUWEVVTVWEUUIVWEUWEUXSVVTVWDUWM
        PVWDUWMPOAPUUKUULUUMYJUUNYKUUOYLYHUWEVWBUXMVWAUWEVWBUXMXSZVVTUXSUYCUWEV
        VTUXSUXMUUPUWEVVTUXSUXMUUQVWFUYBFYMQZFUYBYMQZUYCUYBFFUURZYMQZVWIFUNQVWG
        UYBYNGUYBVWIYSVWJUYBVWIFFYOYOUUSZUXTBCFFYPZYQVWLUYBVWIYNYRUVKUUTUYBVWIF
        UVAUVBVWFFUXLUNQZUXLUYBYMQZVWHUXMUWEVWMVWBUXLFYOUVCYJUXLYNGVWFUXLUYBYSZ
        VWNUWNEUXKUXKVWIVWKUXIBCFFYPYQUVDUWEVWBVWOUXMUWEVWBIZUAUXLUYBUYEUXLGUYE
        UXKGZUYKUWMOZIVWPUYEUYBGZUWNVWREUYEUXKVVQUWLUYKUWMVVRUVLUVEVWPVWRVWQVWS
        VWPVWRVWQVWSVWPVWRIZUYEUYOOZUXJIZCVLBVLVXAUYAIZCVLBVLVWQVWSVWTVXBVXCBCV
        WTVXBVXCVWTVXBIZVXAUWSUXTVWTVXAUXJYEVWTVXAUWSUXIWCVXDUXCUYKUWMVXAUXCUYK
        OVWTUXJVXAUYKVUDUXCVXAUYGUYTUYJVUCNVXAUYFUYSJKUYEUYOUFVMVJVXAUYIVUBDMVX
        AUYHVUAJKUYEUYOUGVMVJVKVNVUFUVFWBVWPVWRVXBWIUVMYTYGUVGUXJBCUYEVIUYABCUY
        EVIUVHUVIUVJYHUVNUVOUXLUYBYNYRUVPFUXLUYBUVQWKUYBFUVRXCYTYKUVSYLUVTUWA
        $.
        $( [19-Oct-2014] $)
    $}

    $( the only place we use general field division here.  making a deduction to avoid ludicrous antecedents $)
    ${
      pellex.ann $e |- ( ph -> A e. NN ) $. $( A,B first pigeon $)
      pellex.bnn $e |- ( ph -> B e. NN ) $.
      pellex.cz $e |- ( ph -> C e. ZZ ) $. $( common norm $)
      pellex.dnn $e |- ( ph -> D e. NN ) $. $( discriminant $)
      pellex.irr $e |- ( ph -> -. ( sqr ` D ) e. QQ ) $.
      pellex.enn $e |- ( ph -> E e. NN ) $. $( E,F second pigeon $)
      pellex.fnn $e |- ( ph -> F e. NN ) $.
      pellex.neq $e |- ( ph -> -. ( A = E /\ B = F ) ) $.
      pellex.cn0 $e |- ( ph -> C =/= 0 ) $.
      pellex.no1 $e |- ( ph -> ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = C ) $.
      pellex.no2 $e |- ( ph -> ( ( E ^ 2 ) - ( D x. ( F ^ 2 ) ) ) = C ) $.
      pellex.xcg $e |- ( ph -> ( A mod ( abs ` C ) ) = ( E mod ( abs ` C ) ) )
          $.
      pellex.ycg $e |- ( ph -> ( B mod ( abs ` C ) ) = ( F mod ( abs ` C ) ) )
          $.

      $(
        math form:

        |(A+dB)/(E+dF)| = |(A+dB)(E-dF) / (E+dF)(E-dF)| = |(AE-DBF)+d(BE-AF)| / |EE+DFF=C| is the soln
        norm: (AE-DBF)(AE-DBF)-D(BE-AF)(BE-AF) / CC;
        AAEE-2AEDBF+DDBBFF-DBBEE+2DBEAF-DAAFF / CC
        AAEE+DDBBFF-DBBEE-DAAFF / CC
        (AA-DBB)EE-DFF(AA-DBB) / CC
        EE-DFF / C
        1
        divisibility: AE-DBF ~~ AA-DBB ~ C ~ 0 mod C; BE-AF ~~ FE-FE ~ 0
        nontriviality: via the norm, AE-DBF=0 implies d = AF-BE / CC contradicting irrationality.  BE-AF=0 means B/A = F/E = r; common norm then implies B=A and F=E
      $)


      $( Lemma for ~ pellex .  Doing a field division between near solutions
         get us to norm 1, and the modularity constraint ensures we still have
         an integer.  Returning NN guarantees that we are not returning the
         trivial solution (1,0). $)
      pellexlem6 $p |- ( ph -> E. a e. NN E. b e. NN ( ( a ^ 2 ) - ( D x. ( b ^
          2 ) ) ) = 1 ) $=
        ( cmul co cmin cdiv cabs cfv cn wcel c2 cexp c1 wceq cv wrex cz cc0 wne
        cc nncn syl mulcl syl2anc subcl absdiv syl3anc cneg caddc negsub eqcomd
        cmo oveq1d nnre remulcl renegcl nnz modmul1 syl221anc sqcl sqval resqcl
        cr resubcl 0re abscl divid eqeltrd wb mod0 mpbird absmod0 eqtrd modadd1
        a1i oveq2d mul12 3eqtrd negid mpbid redivcl wn cle wbr clt wa cn0 nnnn0
        absz nn0ge0 divcl syl22anc adantr ex mtod absresq sqdiv sqne0 syl112anc
        adantl mulsub addcl subdi adddi mulcom mulass sqmul subdir eqidd negeqd
        oveq12d w3a simpr fveq2d df-ne jca oveq1 divcan1 csqr ad2antrr zcn recn
        crp absrpcl npcan eqtr2d rpne0 zre 0mod eqtr4d addid2 zmulcl lt01 ltnle
        1z 1re mp2an sqge0 mulge0 suble0 breq1 divass divsubdir nnncan2 addsub4
        mpbi mul4 negsubdi2 mulneg2 mulneg1 div0 abs0 sq0 sylibr divne0 nnabscl
        3eqtr4d nnne0 biimprd divcan4 3syl nngt0 divge0 sqrsq fveq2 sqr1 simplr
        divmuleq eqtr3d mulid2 syld mpd subeq0 necon3bid eqeq1d rcla42ev ) ABFU
        CUDZECGUCUDZUCUDZUEUDZDUFUDZUGUHZUIUJZCFUCUDZBGUCUDZUEUDZDUFUDZUGUHZUIU
        JZUXBUKULUDZEUXHUKULUDZUCUDZUEUDZUMUNZHUOZUKULUDZEIUOZUKULUDZUCUDZUEUDZ
        UMUNZIUIUPHUIUPAUXAUQUJZUXAURUSZUXCAUYBUXBUQUJZAUXBUWTUGUHZDUGUHZUFUDZU
        QAUWTUTUJZDUTUJZDURUSZUXBUYGUNAUWQUTUJZUWSUTUJZUYHABUTUJZFUTUJZUYKABUIU
        JZUYMJBVAVBZAFUIUJZUYNOFVAVBZBFVCVDZAEUTUJZUWRUTUJZUYLAEUIUJZUYTMEVAVBZ
        ACUTUJZGUTUJZVUAACUIUJZVUDKCVAVBZAGUIUJZVUEPGVAVBZCGVCVDZEUWRVCVDZUWQUW
        SVEVDZADUQUJZUYILDUUAVBZRUWTDVFVGAUYEUYFVLUDURUNZUYGUQUJZAUWTUYFVLUDZUR
        UNZVUOAVUQURUYFVLUDZURAVUQUWQUWSVHZVIUDZUYFVLUDZUWSVUTVIUDZUYFVLUDZVUSA
        UWTVVAUYFVLAVVAUWTAUYKUYLVVAUWTUNUYSVUKUWQUWSVJVDVKVMAUWQWCUJZUWSWCUJZV
        UTWCUJZUYFUUCUJZUWQUYFVLUDZUWSUYFVLUDZUNVVBVVDUNABWCUJZFWCUJZVVEAUYOVVK
        JBVNVBZAUYQVVLOFVNVBZBFVOVDZAEWCUJZUWRWCUJZVVFAVUBVVPMEVNVBZACWCUJZGWCU
        JZVVQAVUFVVSKCVNVBZAVUHVVTPGVNVBZCGVOVDEUWRVOVDZAVVFVVGVWCUWSVPVBAUYIUY
        JVVHVUNRDUUDVDZAVVIFFUCUDZUYFVLUDZGEGUCUDZUCUDZUYFVLUDZVVJAVVKVVLFUQUJZ
        VVHBUYFVLUDFUYFVLUDUNZVVIVWFUNVVMVVNAUYQVWJOFVQVBZVWDUABFFUYFVRVSAVWFFU
        KULUDZEGUKULUDZUCUDZUEUDZVWOVIUDZUYFVLUDZURVWOVIUDZUYFVLUDZVWIAVWEVWQUY
        FVLAVWQVWMVWEAVWMUTUJZVWOUTUJZVWQVWMUNAUYNVXAUYRFVTVBZAUYTVWNUTUJZVXBVU
        CAVUEVXDVUIGVTVBZEVWNVCVDZVWMVWOUUEVDAUYNVWMVWEUNUYRFWAVBUUFVMAVWPWCUJZ
        URWCUJZVWOWCUJZVVHVWPUYFVLUDZVUSUNVWRVWTUNAVWMWCUJZVXIVXGAVVLVXKVVNFWBV
        BAVVPVWNWCUJZVXIVVRAVVTVXLVWBGWBVBEVWNVOVDZVWMVWOWDVDVXHAWEWOZVXMVWDAVX
        JDUYFVLUDZVUSAVWPDUYFVLTVMAVXOURVUSAVXOURUNZUYFUYFVLUDURUNZAVXQUYFUYFUF
        UDZUQUJZAVXRUMUQAUYFUTUJZUYFURUSZVXRUMUNAUYFWCUJZVXTAUYIVYBVUNDWFVBZUYF
        UUBVBAVVHVYAVWDUYFUUGVBUYFWGVDUMUQUJAUUOWOWHAVYBVVHVXQVXSWIVYCVWDUYFUYF
        WJVDWKADWCUJZVVHVXPVXQWIAVUMVYDLDUUHVBZVWDDUYFWLVDWKAVVHVUSURUNVWDUYFUU
        IVBZUUJWMVWPURVWOUYFWNVSAVWSVWHUYFVLAVWSVWOEGGUCUDZUCUDZVWHAVXBVWSVWOUN
        VXFVWOUUKVBAVWNVYGEUCAVUEVWNVYGUNVUIGWAVBWPAUYTVUEVUEVYHVWHUNVUCVUIVUIE
        GGWQVGWRVMWRAVWICVWGUCUDZUYFVLUDZVVJAVVTVVSVWGUQUJZVVHGUYFVLUDZCUYFVLUD
        ZUNVWIVYJUNVWBVWAAEUQUJZGUQUJZVYKAVUBVYNMEVQVBAVUHVYOPGVQVBZEGUULVDVWDA
        VYMVYLUBVKGCVWGUYFVRVSAVYIUWSUYFVLAVUDUYTVUEVYIUWSUNVUGVUCVUICEGWQVGVMW
        MWRUWQUWSVUTUYFWNVSAVVCURUYFVLAUYLVVCURUNVUKUWSWSVBVMWRVYFWMAUWTWCUJZVV
        HVURVUOWIAVVEVVFVYQVVOVWCUWQUWSWDVDZVWDUWTUYFWLVDWTAUYEWCUJZVVHVUOVUPWI
        AUYHVYSVULUWTWFVBVWDUYEUYFWJVDWTWHAUXAWCUJZUYBUYDWIAVYQVYDUYJVYTVYRVYER
        UWTDXAVGZUXAXIVBWKAUYHUWTURUSZUYIUYJUYCVULAUWTURUNZXBWUBAWUCUMURUXLUEUD
        ZUNZAWUEUMURXCXDZWUFXBZAURUMXEXDZWUGUUMVXHUMWCUJWUHWUGWIWEUUPURUMUUNUUQ
        UVFWOAWUEWUFAWUEXFWUFWUDURXCXDZAWUIWUEAWUIURUXLXCXDZAVVPUREXCXDZUXKWCUJ
        ZURUXKXCXDZWUJVVRAEXGUJZWUKAVUBWUNMEXHVBEXJVBAUXHWCUJZWULAUXGUTUJZWUOAU
        XFUTUJZUYIUYJWUPAUXDUTUJZUXEUTUJZWUQAVUDUYNWURVUGUYRCFVCVDZAUYMVUEWUSUY
        PVUIBGVCVDZUXDUXEVEVDZVUNRUXFDXKVGUXGWFVBZUXHWBVBZAWUOWUMWVCUXHUURVBEUX
        KUUSXLAVXHUXLWCUJZWUIWUJWIVXNAVVPWULWVEVVRWVDEUXKVOVDURUXLUUTVDWKXMWUEW
        UFWUIWIAUMWUDURXCUVAXTWKXNXOAWUCWUEAWUCXFZUMUXMWUDWUDWVFUXMUMAUXNWUCAUX
        MUWTUWTUCUDZDUKULUDZUFUDZEUXFUXFUCUDZUCUDZWVHUFUDZUEUDZWVGWVKUEUDZWVHUF
        UDZUMAUXJWVIUXLWVLUEAUXJUXAUKULUDZUWTUKULUDZWVHUFUDZWVIAVYTUXJWVPUNWUAU
        XAXPVBAUYHUYIUYJWVPWVRUNVULVUNRUWTDXQVGAWVQWVGWVHUFAUYHWVQWVGUNVULUWTWA
        VBVMWRAUXLEUXFUKULUDZWVHUFUDZUCUDZEWVSUCUDZWVHUFUDZWVLAUXKWVTEUCAUXKUXG
        UKULUDZWVTAUXGWCUJZUXKWWDUNAUXFWCUJZVYDUYJWWEAUXDWCUJZUXEWCUJZWWFAVVSVV
        LWWGVWAVVNCFVOVDZAVVKVVTWWHVVMVWBBGVOVDZUXDUXEWDVDZVYERUXFDXAVGZUXGXPVB
        AWUQUYIUYJWWDWVTUNWVBVUNRUXFDXQVGWMWPAWWCWWAAUYTWVSUTUJZWVHUTUJZWVHURUS
        ZWWCWWAUNVUCAWUQWWMWVBUXFVTVBAUYIWWNVUNDVTVBZAWWOUYJRAUYIWWOUYJWIVUNDXR
        VBWKZEWVSWVHUVBXSVKAWWBWVKWVHUFAWVSWVJEUCAWUQWVSWVJUNWVBUXFWAVBWPVMWRYK
        AWVOWVMAWVGUTUJZWVKUTUJZWWNWWOWVOWVMUNAUYHUYHWWRVULVULUWTUWTVCVDAUYTWVJ
        UTUJZWWSVUCAWUQWUQWWTWVBWVBUXFUXFVCVDEWVJVCVDWWPWWQWVGWVKWVHUVCXSVKAWVO
        UWQUWQUCUDZUWSUWSUCUDZVIUDZUWQUWSUCUDZWXDVIUDZUEUDZEUXDUXDUCUDZUCUDZEUX
        EUXEUCUDZUCUDZVIUDZEUXDUXEUCUDZUCUDZWXMVIUDZUEUDZUEUDZWVHUFUDWVHWVHUFUD
        ZUMAWVNWXPWVHUFAWVGWXFWVKWXOUEAUYKUYLUYKUYLWVGWXFUNUYSVUKUYSVUKUWQUWSUW
        QUWSYAXLAWVKEWXGWXIVIUDZWXLWXLVIUDZUEUDZUCUDZWXOAWVJWXTEUCAWURWUSWURWUS
        WVJWXTUNWUTWVAWUTWVAUXDUXEUXDUXEYAXLWPAWYAEWXRUCUDZEWXSUCUDZUEUDZWXOAUY
        TWXRUTUJZWXSUTUJZWYAWYDUNVUCAWXGUTUJZWXIUTUJZWYEAWURWURWYGWUTWUTUXDUXDV
        CVDZAWUSWUSWYHWVAWVAUXEUXEVCVDZWXGWXIYBVDAWXLUTUJZWYKWYFAWURWUSWYKWUTWV
        AUXDUXEVCVDZWYLWXLWXLYBVDEWXRWXSYCVGAWYBWXKWYCWXNUEAUYTWYGWYHWYBWXKUNVU
        CWYIWYJEWXGWXIYDVGAUYTWYKWYKWYCWXNUNVUCWYLWYLEWXLWXLYDVGYKWMWMYKVMAWXPW
        VHWVHUFAWXPWXCWXNUEUDZWXOUEUDZWXCWXKUEUDZWVHAWXFWYMWXOUEAWXEWXNWXCUEAWX
        DWXMWXDWXMVIAWXDUWSUWQUCUDZEUWRUWQUCUDZUCUDZWXMAUYKUYLWXDWYPUNUYSVUKUWQ
        UWSYEVDAUYTVUAUYKWYPWYRUNVUCVUJUYSEUWRUWQYFVGAWYQWXLEUCAWYQUWRFBUCUDZUC
        UDZUXDGBUCUDZUCUDZWXLAUWQWYSUWRUCAUYMUYNUWQWYSUNUYPUYRBFYEVDWPAVUDVUEUY
        NUYMWYTXUBUNVUGVUIUYRUYPCGFBUVGXLAXUAUXEUXDUCAVUEUYMXUAUXEUNVUIUYPGBYEV
        DWPWRWPWRZXUCYKWPVMAWXCUTUJZWXKUTUJZWXNUTUJZWYNWYOUNAWXAUTUJZWXBUTUJZXU
        DAUYKUYKXUGUYSUYSUWQUWQVCVDZAUYLUYLXUHVUKVUKUWSUWSVCVDZWXAWXBYBVDAWXHUT
        UJZWXJUTUJZXUEAUYTWYGXUKVUCWYIEWXGVCVDZAUYTWYHXULVUCWYJEWXIVCVDZWXHWXJY
        BVDAWXMUTUJZXUOXUFAUYTWYKXUOVUCWYLEWXLVCVDZXUPWXMWXMYBVDWXCWXKWXNUVDVGA
        WYOWXAWXHUEUDZWXBWXJUEUDZVIUDZUWQUKULUDZEUXDUKULUDZUCUDZUEUDZUWSUKULUDZ
        EUXEUKULUDZUCUDZUEUDZVIUDZWVHAXUGXUHXUKXULWYOXUSUNXUIXUJXUMXUNWXAWXBWXH
        WXJUVEXLAXVHXUSAXVCXUQXVGXURVIAXUTWXAXVBWXHUEAUYKXUTWXAUNUYSUWQWAVBAXVA
        WXGEUCAWURXVAWXGUNWUTUXDWAVBWPYKAXVDWXBXVFWXJUEAUYLXVDWXBUNVUKUWSWAVBAX
        VEWXIEUCAWUSXVEWXIUNWVAUXEWAVBWPYKYKVKAXVHBUKULUDZVWMUCUDZECUKULUDZUCUD
        ZVWMUCUDZUEUDZEEUCUDZXVKUCUDZVWNUCUDZEXVIUCUDZVWNUCUDZUEUDZVIUDDVWMUCUD
        ZEDUCUDZVHZVWNUCUDZVIUDZWVHAXVCXVNXVGXVTVIAXUTXVJXVBXVMUEAUYMUYNXUTXVJU
        NUYPUYRBFYGVDAXVBEXVKVWMUCUDZUCUDZXVMAXVAXWFEUCAVUDUYNXVAXWFUNVUGUYRCFY
        GVDWPAXVMXWGAUYTXVKUTUJZVXAXVMXWGUNVUCAVUDXWHVUGCVTVBZVXCEXVKVWMYFVGVKW
        MYKAXVDXVQXVFXVSUEAXVDEUKULUDZUWRUKULUDZUCUDZXVOXVKVWNUCUDZUCUDZXVQAUYT
        VUAXVDXWLUNVUCVUJEUWRYGVDAXWJXVOXWKXWMUCAUYTXWJXVOUNVUCEWAVBAVUDVUEXWKX
        WMUNVUGVUICGYGVDYKAXVQXWNAXVOUTUJZXWHVXDXVQXWNUNAUYTUYTXWOVUCVUCEEVCVDZ
        XWIVXEXVOXVKVWNYFVGVKWRAXVFEXVIVWNUCUDZUCUDZXVSAXVEXWQEUCAUYMVUEXVEXWQU
        NUYPVUIBGYGVDWPAXVSXWRAUYTXVIUTUJZVXDXVSXWRUNVUCAUYMXWSUYPBVTVBZVXEEXVI
        VWNYFVGVKWMYKYKAXVNXWAXVTXWDVIAXVNXVIXVLUEUDZVWMUCUDZXWAXWAAXXBXVNAXWSX
        VLUTUJZVXAXXBXVNUNXWTAUYTXWHXXCVUCXWIEXVKVCVDZVXCXVIXVLVWMYHVGVKAXXADVW
        MUCSVMAXWAYIWRAXVTXVPXVRUEUDZVWNUCUDZEXVLUCUDZXVRUEUDZVWNUCUDXWDAXXFXVT
        AXVPUTUJZXVRUTUJZVXDXXFXVTUNAXWOXWHXXIXWPXWIXVOXVKVCVDAUYTXWSXXJVUCXWTE
        XVIVCVDVXEXVPXVRVWNYHVGVKAXXEXXHVWNUCAXVPXXGXVRUEAUYTUYTXWHXVPXXGUNVUCV
        UCXWIEEXVKYFVGVMVMAXXHXWCVWNUCAXXHEXVLXVIUEUDZUCUDZEDVHZUCUDZXWCAUYTXXC
        XWSXXHXXLUNVUCXXDXWTUYTXXCXWSYLXXLXXHEXVLXVIYCVKVGAXXKXXMEUCAXXKXXAVHZX
        XMAXWSXXCXXKXXOUNXWTXXDXWSXXCXFXXOXXKXVIXVLUVHVKVDAXXADSYJWMWPAUYTUYIXX
        NXWCUNVUCVUNEDUVIVDWRVMWRYKAXWEXWADVWOUCUDZVHZVIUDZXWAXXPUEUDZWVHAXWDXX
        QXWAVIAXWDXWBVWNUCUDZVHZXXQAXWBUTUJZVXDXWDXYAUNAUYTUYIXYBVUCVUNEDVCVDVX
        EXWBVWNUVJVDAXXTXXPAXXTDEUCUDZVWNUCUDZXXPAXWBXYCVWNUCAUYTUYIXWBXYCUNVUC
        VUNEDYEVDVMAUYIUYTVXDXYDXXPUNVUNVUCVXEDEVWNYFVGWMYJWMWPAXWAUTUJZXXPUTUJ
        ZXXRXXSUNAUYIVXAXYEVUNVXCDVWMVCVDAUYIVXBXYFVUNVXFDVWOVCVDXWAXXPVJVDAXXS
        DVWPUCUDZDDUCUDZWVHAUYIVXAVXBXXSXYGUNVUNVXCVXFUYIVXAVXBYLXYGXXSDVWMVWOY
        CVKVGAVWPDDUCTWPAWVHXYHAUYIWVHXYHUNVUNDWAVBVKWRWRWRWRWRVMAWWNWWOWXQUMUN
        WWPWWQWVHWGVDWRWRZXMVKWVFUXJURUXLUEWVFUXJURUKULUDZURWVFUXBURUKULWVFUXBU
        RDUFUDZUGUHZURWVFUXAXYKUGWVFUWTURDUFAWUCYMVMYNAXYLURUNWUCAXYLURUGUHZURA
        XYKURUGAUYIUYJXYKURUNVUNRDUVKVDYNXYMURUNAUVLWOWMXMWMVMXYJURUNWVFUVMWOWM
        VMWVFWUDYIWRXNXOUWTURYOUVNVUNRUWTDUVOXLUXAUVPVDAUXGUQUJZUXGURUSZUXIAXYN
        UXHUQUJZAUXHUXFUGUHZUYFUFUDZUQAWUQUYIUYJUXHXYRUNWVBVUNRUXFDVFVGAXYQUYFV
        LUDURUNZXYRUQUJZAUXFUYFVLUDZURUNZXYSAYUAVUSURAYUAUXDUXEVHZVIUDZUYFVLUDZ
        UXEYUCVIUDZUYFVLUDZVUSAUXFYUDUYFVLAWURWUSUXFYUDUNWUTWVAWURWUSXFYUDUXFUX
        DUXEVJVKVDVMAWWGWWHYUCWCUJZVVHUXDUYFVLUDZUXEUYFVLUDZUNYUEYUGUNWWIWWJAWW
        HYUHWWJUXEVPVBVWDAGFUCUDZUYFVLUDZFGUCUDZUYFVLUDZYUIYUJAYUKYUMUYFVLAVUEU
        YNYUKYUMUNVUIUYRGFYEVDVMAVVSVVTVWJVVHVYMVYLUNYUIYULUNVWAVWBVWLVWDUBCGFU
        YFVRVSAVVKVVLVYOVVHVWKYUJYUNUNVVMVVNVYPVWDUABFGUYFVRVSUVQUXDUXEYUCUYFWN
        VSAYUFURUYFVLAWUSYUFURUNWVAUXEWSVBVMWRVYFWMAWWFVVHYUBXYSWIWWKVWDUXFUYFW
        LVDWTAXYQWCUJZVVHXYSXYTWIAWUQYUOWVBUXFWFVBVWDXYQUYFWJVDWTWHAWWEXYNXYPWI
        WWLUXGXIVBWKAWUQUXFURUSZUYIUYJXYOWVBAYUPUXDUXEUSZAUXDUXEUNZXBYUQAYURBFU
        NZCGUNZXFZQAYURCGUFUDZBFUFUDZUNZYVAAYVDYURAVUDUYMVUEGURUSZXFUYNFURUSZXF
        YVDYURWIVUGUYPAVUEYVEVUIAVUHYVEPGUVRVBZYPAUYNYVFUYRAUYQYVFOFUVRVBZYPCBG
        FUWHXLUVSAYVDYVAAYVDXFZYVBUKULUDZUMUNZYVAYVIYVJYVJDUCUDZDUFUDZXXAXXAUFU
        DZUMYVIYVMYVJYVIYVJUTUJZUYIUYJYVMYVJUNAYVOYVDAYVBUTUJZYVOAVUDVUEYVEYVPV
        UGVUIYVGCGXKVGYVBVTVBXMZAUYIYVDVUNXMAUYJYVDRXMYVJDUVTVGVKYVIYVLXXADXXAU
        FYVIYVLYVJVWPUCUDZYVJVWMUCUDZYVJVWOUCUDZUEUDZXXAYVIDVWPYVJUCYVIVWPDAVWP
        DUNYVDTXMVKWPYVIYVOVXAVXBYVRYWAUNYVQAVXAYVDVXCXMZAVXBYVDVXFXMYVJVWMVWOY
        CVGYVIYVSXVIYVTXVLUEYVIYVSYVCUKULUDZVWMUCUDZXVIVWMUFUDZVWMUCUDZXVIYVDYV
        SYWDUNAYVDYVJYWCVWMUCYVBYVCUKULYQVMXTYVIYWCYWEVWMUCYVIUYMUYNYVFYWCYWEUN
        AUYMYVDUYPXMAUYNYVDUYRXMAYVFYVDYVHXMBFXQVGVMYVIXWSVXAVWMURUSZYWFXVIUNAX
        WSYVDXWTXMYWBAYWGYVDAYWGYVFYVHAUYNYWGYVFWIUYRFXRVBWKXMXVIVWMYRVGWRYVIYV
        TEYVJVWNUCUDZUCUDZEXVKVWNUFUDZVWNUCUDZUCUDXVLYVIYVOUYTVXDYVTYWIUNYVQAUY
        TYVDVUCXMAVXDYVDVXEXMZYVJEVWNWQVGYVIYWHYWKEUCYVIYVJYWJVWNUCYVIVUDVUEYVE
        YVJYWJUNAVUDYVDVUGXMAVUEYVDVUIXMAYVEYVDYVGXMCGXQVGVMWPYVIYWKXVKEUCYVIXW
        HVXDVWNURUSZYWKXVKUNAXWHYVDXWIXMYWLAYWMYVDAYWMYVEYVGAVUEYWMYVEWIVUIGXRV
        BWKXMXVKVWNYRVGWPWRYKWRADXXAUNYVDAXXADSVKXMYKAYVNUMUNYVDAYVNDDUFUDZUMAX
        XADXXADUFSSYKAUYIUYJYWNUMUNVUNRDWGVDWMXMWRYVIYVKYVBUMUNZYVAYVIYVKYWOYVI
        YVKXFZYVBYVJYSUHZUMYSUHZUMAYVBYWQUNYVDYVKAYWQYVBAYVBWCUJZURYVBXCXDZYWQY
        VBUNAVVSVVTYVEYWSVWAVWBYVGCGXAVGAVVSURCXCXDZVVTURGXEXDZYWTVWAAVUFCXGUJY
        XAKCXHCXJUWAVWBAVUHYXBPGUWBVBCGUWCXLYVBUWDVDVKYTYVKYWQYWRUNYVIYVJUMYSUW
        EXTYWRUMUNYWPUWFWOWRXNYVIYWOYVAYVIYWOXFZYUSYUTYXCBYVCFUCUDZUMFUCUDZFYXC
        YXDBAYXDBUNZYVDYWOAUYMUYNYVFYXFUYPUYRYVHBFYRVGYTVKYXCYVCUMFUCYXCYVBYVCU
        MAYVDYWOUWGYVIYWOYMZUWIVMAYXEFUNZYVDYWOAUYNYXHUYRFUWJVBYTWRYXCCYVBGUCUD
        ZUMGUCUDZGYXCYXICAYXICUNZYVDYWOAVUDVUEYVEYXKVUGVUIYVGCGYRVGYTVKYXCYVBUM
        GUCYXGVMAYXJGUNZYVDYWOAVUEYXLVUIGUWJVBYTWRYPXNUWKUWLXNUWKXOUXDUXEYOUVNA
        UXFURUXDUXEAWURWUSUXFURUNYURWIWUTWVAUXDUXEUWMVDUWNWKVUNRUXFDUVOXLUXGUVP
        VDXYIUYAUXNUXJUXSUEUDZUMUNHIUXBUXHUIUIUXOUXBUNZUXTYXMUMYXNUXPUXJUXSUEUX
        OUXBUKULYQVMUWOUXQUXHUNZYXMUXMUMYXOUXSUXLUXJUEYXOUXRUXKEUCUXQUXHUKULYQW
        PWPUWOUWPVG $.
        $( [19-Oct-2014] $)
    $}

    ${
      $d D x y $.
      $( Every Pell equation has a nontrivial solution.  Lemma 62 in
         [vandenDries]. $)
      pellex $p |- ( ( D e. NN /\ -. ( sqr ` D ) e. QQ ) -> E. x e. NN E. y e.
          NN ( ( x ^ 2 ) - ( D x. ( y ^ 2 ) ) ) = 1 ) $=
        ( vb vc vf vg cn wcel cfv wa cv c2 cexp co wceq wbr c1st cmo c2nd va vd
        ve csqr cq wn cc0 wne cmul cmin copab cen cz wrex c1 pellexlem5 cop cfz
        cabs cxp cvv csdm nnex xpex opabssxp ssexi a1i com fzfi mp2an isfinite3
        cfn xpfi biimpi ax-mp nnenom omex ensym pm3.2i sdomentr mp2 syl jca imp
        simprr syl2anc sseli simprrl nnz simpllr simplr nnabscl zmodfz ex elxp7
        simprrr ovex opelxp 3imtr4g syl5 adantlrr fveq2 oveq1d opeq12d fphpd wi
        weq wb eleq1 adantr adantl anbi12d oveq1 oveq2d oveq12d eqeq1d cbvopabv
        eleq2i anim2i wex elopab w3a 3expb 3ad2ant1 simp1lr ad3antrrr simp3 vex
        3adant2l opth sylib syl3anc fveq2d op1st eqtrd 3eqtr3d op2nd mpd syl5bi
        exlimdvv simp3ll simp3lr 3adant1r simp2ll simp2lr simp2l simp1rl simp3l
        simpl simpr simp2 simp1 neeq12d mpbid necon3abii simp1rr simp2rr simp3r
        3adant1l simprl simpll 3adant3 simpld simprd pellexlem6 3exp rexlimdvva
        imp3a mpdan rexlimdva ) CHIZCUDJUEIUFZKZUALZUGUHZDLZHIZELZHIZKZUVPMNOZC
        UVRMNOZUIOZUJOZUVNPZKZDEUKZHULQZKZUAUMUNALMNOCBLMNOUIOUJOUOPBHUNAHUNZUA
        DECUPUVMUWIUWJUAUMUVMUVNUMIZKZUWIUWJUWLUWIKZUBLZUCLZUHZUWNRJZUVNUSJZSOZ
        UWNTJZUWRSOZUQZUWORJZUWRSOZUWOTJZUWRSOZUQZPZKZUCUWGUNUBUWGUNZUWJUWMUBUC
        UWGUGUWRUOUJOZUROZUXLUTZUXBUXGUWMUWGVAIZUXMHVBQZHUWGULQZKZUXMUWGVBQZUXN
        UWMUWGHHUTZHHVCVCVDUWEDEHHVEZVFVGUWMUXOUXPUXOUWMHVAIUXMVHVBQZVHHULQZKUX
        OVCUYAUYBUXMVLIZUYAUXLVLIZUYDUYCUGUXKVIZUYEUXLUXLVMVJUYCUYAUXMVKVNVOHVH
        ULQUYBVPHVHVQVRVOVSUXMVHHVAVTWAVGUWMUWHUXPUWLUVOUWHWEUWGHVCVRWBWCUXNUXQ
        UXRUXMHUWGVAVTWDWFUWLUVOUWNUWGIZUXBUXMIZUWHUWLUVOKZUYFUYGUYFUWNUXSIZUYH
        UYGUWGUXSUWNUXTWGUYHUWNVAVAUTIZUWQHIZUWTHIZKKZUWSUXLIZUXAUXLIZKZUYIUYGU
        YHUYMUYPUYHUYMKZUYNUYOUYQUWQUMIZUWRHIZUYNUYQUYKUYRUYHUYJUYKUYLWHUWQWIWB
        UYQUWKUVOUYSUVMUWKUVOUYMWJUWLUVOUYMWKUVNWLWFZUWQUWRWMWFUYQUWTUMIZUYSUYO
        UYQUYLVUAUYHUYJUYKUYLWPUWTWIWBUYTUWTUWRWMWFWCWNUWNHHWOUWSUXAUXLUXLUWTUW
        RSWQZWRWSWTWDXAUBUCXGZUWSUXDUXAUXFVUCUWQUXCUWRSUWNUWORXBXCVUCUWTUXEUWRS
        UWNUWOTXBXCXDXEUWLUVOUXJUWJUWHUYHUXJUWJUYHUXIUWJUBUCUWGUWGUYHUYFUWOUWGI
        ZKZKZUXIUWJVUFUXIUWJUYHVUEUXIUWJXFZVUEUYFUWOFLZHIZGLZHIZKZVUHMNOZCVUJMN
        OZUIOZUJOZUVNPZKZFGUKZIZKUYHVUGVUDVUTUYFVUDVUTUWGVUSUWOUWFVURDEFGDFXGZE
        GXGZKZUVTVULUWEVUQVVCUVQVUIUVSVUKVVAUVQVUIXHVVBUVPVUHHXIXJVVBUVSVUKXHVV
        AUVRVUJHXIXKXLVVCUWDVUPUVNVVCUWAVUMUWCVUOUJVVAUWAVUMPVVBUVPVUHMNXMXJVVB
        UWCVUOPVVAVVBUWBVUNCUIUVRVUJMNXMXNXKXOXPXLXQXRVNXSUYHUYFVUTVUGUYFUWNUVP
        UVRUQZPZUWFKZEXTDXTUYHVUTVUGXFZUWFDEUWNYAUYHVVFVVGDEUYHVVFVVGVUTUWOVUHV
        UJUQZPZVURKZGXTFXTUYHVVFKZVUGVURFGUWOYAVVKVVJVUGFGVVKVVJUXIUWJVVKVVJUXI
        YBZUVPUVRUVNCVUHVUJABVVKVVJUVQUXIUYHVVEUWFUVQUVQUVSUWEUYHVVEUUAYCYDVVKV
        VJUVSUXIUYHVVEUWFUVSUVQUVSUWEUYHVVEUUBYCYDUYHVVJUXIUWKVVFUVMUWKUVOVVJUX
        IYEUUCVVKVVJUVKUXIUVMUVKUWKUVOVVFUVKUVLUUIYFYDVVKVVJUVLUXIUVMUVLUWKUVOV
        VFUVKUVLUUJYFYDVVKVURUXIVUIVVIVUIVUKVUQVVKUXIUUDYIVVKVURUXIVUKVVIVUIVUK
        VUQVVKUXIUUEYIVVLVVIVVEUWPVVCUFZVVKVVIVURUXIUUFZVVEUWFUYHVVJUXIUUGZVVKV
        VJUWPUXHUUHVVIVVEUWPYBZVVDVVHUHZVVMVVPUWPVVQVVIVVEUWPYGVVPUWNVVDUWOVVHV
        VIVVEUWPUUKVVIVVEUWPUULUUMUUNVVCVVDVVHUVPUVRVUHVUJDYHZEYHZGYHZYJUUOYKYL
        UWLUVOVVFVVJUXIYEVVFVVJUXIUWEUYHUVTUWEVVEVVJUXIUUPUUSVULVUQVVIVVKUXIUUQ
        VVLUVPUWRSOZVUHUWRSOZPZUVRUWRSOZVUJUWRSOZPZVVLVVEVVIUXHVWCVWFKZVVOVVNVV
        KVVJUWPUXHUURVVEVVIUXHYBZUWSUXDPZUXAUXFPZKZVWGVWHUXHVWKVVEVVIUXHYGUWSUX
        AUXDUXFUWQUWRSWQVUBUXEUWRSWQYJYKVVEVVIVWKVWGXFUXHVVEVVIKZVWKVWGVWLVWKKZ
        VWCVWFVWMUWSUXDVWAVWBVWLVWIVWJUUTVWMUWQUVPUWRSVWMUWQVVDRJZUVPVWMUWNVVDR
        VVEVVIVWKUVAZYMVWNUVPPVWMUVPUVRVVRYNVGYOXCVWMUXCVUHUWRSVWMUXCVVHRJZVUHV
        WMUWOVVHRVVEVVIVWKWKZYMVWPVUHPVWMVUHVUJFYHZYNVGYOXCYPVWMUXAUXFVWDVWEVWL
        VWIVWJWEVWMUWTUVRUWRSVWMUWTVVDTJZUVRVWMUWNVVDTVWOYMVWSUVRPVWMUVPUVRVVRV
        VSYQVGYOXCVWMUXEVUJUWRSVWMUXEVVHTJZVUJVWMUWOVVHTVWQYMVWTVUJPVWMVUHVUJVW
        RVVTYQVGYOXCYPWCWNUVBYRYLZUVCVVLVWCVWFVXAUVDUVEUVFYTYSWNYTYSUVHWTWDWDWN
        UVGWDXAUVIWNUVJYR $.
        $( [19-Oct-2014] $)
    $}
  $}

    $( from now on, all work is in the Pell group, either in ( NN X. ZZ ) or RR $)
    $( multiplication formula $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Pell equations 2: Algebraic number theory of the solution set
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $c Pell1QR Pell14QR Pell1234QR PellFund []NN $.

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $(
    pellmulfo $p |- ( ( D e. NN /\ ( A e. ZZ /\ B e. ZZ /\ ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 ) /\ ( E e. ZZ /\ F e. ZZ /\ ( ( E ^ 2 ) - ( D x. ( F ^ 2 ) ) ) = 1 ) ) -> (   /\ ) ) $=
        ? $.
    $)

    $( reciprocal/conjugate formula $)
    $( pell group is in RR+ - 1Q case $)
    $( extend to both 1Q+4Q using rpreccl $)
    $( 1Q iff > 1 $)
    $( 1Q exists (restate pellex) $)
    $( a minimal 1Q exists [most likely using an order isomorphism and a well-ordering on NN] $)
    $( if a PGE is in [1,PellFund), it equals 1 $)
    $( any PGE equals ` ( Fund ^ ( |_ `` ( ( log `` A ) / ( log `` Fund ) ) ) ) ` $)

    $( define image of ZZ or NN $)
    $( prove non-denseness $)
    $( use logarithms to show all elements are powers of a base $)
    $( value of PellFund ` a*a-1 $)
    $( define Ak, Bk $)
    $( Lucas sequence $)

    $( feasibility study of proving existance of the fundamental theorem and the structure theorem using only Pell1QR and a cancellation law $)

    $( Extend class notation to include the class of quadrant-1 Pell
       solutions. $)
    cpell1qr $a class Pell1QR $.
    $( Extend class notation to include the class of any-quadrant Pell
       solutions. $)
    cpell1234qr $a class Pell1234QR $.
    $( Extend class notation to include the class of positive Pell
       solutions. $)
    cpell14qr $a class Pell14QR $.
    $( Extend class notation to include the Pell-equation fundamental solution
       function. $)
    cpellfund $a class PellFund $.
    $( Extend class notation to include the set of square natural numbers. $)
    csquarenn $a class []NN $.

    $( Define the set of square natural numbers. $)
    df-squarenn $a |- []NN = { x e. NN | ( sqr ` x ) e. QQ } $.

    ${
      $d x y z w $.
      $( Define the solutions of a Pell equation in the first quadrant.  To
         avoid pair pain, we represent this via the canonical embedding into
         the reals. $)
      df-pell1qr $a |- Pell1QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e.
          NN0 E. w e. NN0 ( y = ( z + ( ( sqr ` x ) x. w ) ) /\ ( ( z ^ 2 ) - (
          x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( Define the positive solutions of a Pell equation. $)
      df-pell14qr $a |- Pell14QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e.
          NN0 E. w e. ZZ ( y = ( z + ( ( sqr ` x ) x. w ) ) /\ ( ( z ^ 2 ) - (
          x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( Define the general solutions of a Pell equation. $)
      df-pell1234qr $a |- Pell1234QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E.
          z e. ZZ E. w e. ZZ ( y = ( z + ( ( sqr ` x ) x. w ) ) /\ ( ( z ^ 2 )
          - ( x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( A function mapping Pell discriminants to the corresponding fundamental
         solution. $)
      df-pellfund $a |- PellFund = ( x e. ( NN \ []NN ) |-> sup ( { z e. (
          Pell14QR ` x ) | 1 < z } , RR , `' < ) ) $.
    $}

    ${
      $d y z w D $.  $d y z w A $.
      $( Value of the set of first-quadrant Pell solutions. $)
      pell1qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) = { y e. RR | E.
          z e. NN0 E. w e. NN0 ( y = ( z + ( ( sqr ` D ) x. w ) ) /\ ( ( z ^ 2
          ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( va cv csqr cfv cmul co caddc wceq c2 cexp cmin c1 wa cn0 wrex cr crab
        csquarenn cdif cpell1qr fveq2 oveq1d oveq2d eqeq2d oveq1 eqeq1d anbi12d
        cn 2rexbidv rabbidv df-pell1qr reex rabex fvmpt ) EDAFZBFZEFZGHZCFZIJZK
        JZLZUTMNJZVAVCMNJZIJZOJZPLZQZCRSBRSZATUAUSUTDGHZVCIJZKJZLZVGDVHIJZOJZPL
        ZQZCRSBRSZATUAULUBUCUDVADLZVMWBATWCVLWABCRRWCVFVQVKVTWCVEVPUSWCVDVOUTKW
        CVBVNVCIVADGUEUFUGUHWCVJVSPWCVIVRVGOVADVHIUIUGUJUKUMUNEABCUOWBATUPUQUR
        $.
        $( [17-Sep-2014] $)

      $( Membership in a first-quadrant Pell solution set. $)
      elpell1qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e.
          RR /\ E. z e. NN0 E. w e. NN0 ( A = ( z + ( ( sqr ` D ) x. w ) ) /\ (
          ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn cdif wcel cfv cv cmul co wceq c2 cexp wa cn0 wrex cr
        cpell1qr csqr caddc cmin c1 crab pell1qrval eleq2d eqeq1 2rexbidv elrab
        anbi1d syl6bb ) DFGHIZCDUAJZICEKZAKZDUBJBKZLMUCMZNZUQOPMDUROPMLMUDMUENZ
        QZBRSARSZETUFZICTICUSNZVAQZBRSARSZQUNUOVDCEABDUGUHVCVGECTUPCNZVBVFABRRV
        HUTVEVAUPCUSUIULUJUKUM $.
        $( [17-Sep-2014] $)

      $( Value of the set of positive Pell solutions. $)
      pell14qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) = { y e. RR |
          E. z e. NN0 E. w e. ZZ ( y = ( z + ( ( sqr ` D ) x. w ) ) /\ ( ( z ^
          2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( va cv csqr cfv cmul co caddc wceq c2 cexp cmin c1 cz wrex cn0 cr crab
        wa cn csquarenn cdif cpell14qr fveq2 oveq1d oveq2d eqeq2d oveq1 anbi12d
        eqeq1d 2rexbidv rabbidv df-pell14qr reex rabex fvmpt ) EDAFZBFZEFZGHZCF
        ZIJZKJZLZVAMNJZVBVDMNJZIJZOJZPLZUBZCQRBSRZATUAUTVADGHZVDIJZKJZLZVHDVIIJ
        ZOJZPLZUBZCQRBSRZATUAUCUDUEUFVBDLZVNWCATWDVMWBBCSQWDVGVRVLWAWDVFVQUTWDV
        EVPVAKWDVCVOVDIVBDGUGUHUIUJWDVKVTPWDVJVSVHOVBDVIIUKUIUMULUNUOEABCUPWCAT
        UQURUS $.
        $( [17-Sep-2014] $)

      $( Membership in the set of positive Pell solutions. $)
      elpell14qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A
          e. RR /\ E. z e. NN0 E. w e. ZZ ( A = ( z + ( ( sqr ` D ) x. w ) ) /\
          ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn wcel cfv cv cmul co wceq c2 cexp wa cz wrex cn0 cr c1
        cdif cpell14qr csqr caddc cmin pell14qrval eleq2d eqeq1 anbi1d 2rexbidv
        crab elrab syl6bb ) DFGUBHZCDUCIZHCEJZAJZDUDIBJZKLUELZMZURNOLDUSNOLKLUF
        LUAMZPZBQRASRZETULZHCTHCUTMZVBPZBQRASRZPUOUPVECEABDUGUHVDVHECTUQCMZVCVG
        ABSQVIVAVFVBUQCUTUIUJUKUMUN $.
        $( [17-Sep-2014] $)

      $( Value of the set of general Pell solutions. $)
      pell1234qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell1234QR ` D ) = { y e.
          RR | E. z e. ZZ E. w e. ZZ ( y = ( z + ( ( sqr ` D ) x. w ) ) /\ ( (
          z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( vd cv csqr cfv cmul co caddc wceq c2 cexp cmin c1 wa cz wrex cr fveq2
        crab cn csquarenn cpell1234qr oveq1d oveq2d eqeq2d oveq1 eqeq1d anbi12d
        cdif 2rexbidv rabbidv df-pell1234qr reex rabex fvmpt ) EDAFZBFZEFZGHZCF
        ZIJZKJZLZUTMNJZVAVCMNJZIJZOJZPLZQZCRSBRSZATUBUSUTDGHZVCIJZKJZLZVGDVHIJZ
        OJZPLZQZCRSBRSZATUBUCUDULUEVADLZVMWBATWCVLWABCRRWCVFVQVKVTWCVEVPUSWCVDV
        OUTKWCVBVNVCIVADGUAUFUGUHWCVJVSPWCVIVRVGOVADVHIUIUGUJUKUMUNEABCUOWBATUP
        UQUR $.
        $( [17-Sep-2014] $)

      $( Membership in the set of general Pell solutions. $)
      elpell1234qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1234QR ` D ) <->
          ( A e. RR /\ E. z e. ZZ E. w e. ZZ ( A = ( z + ( ( sqr ` D ) x. w ) )
          /\ ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn cdif wcel cfv cv cmul co wceq c2 cexp wa cz wrex cr
        cpell1234qr csqr caddc cmin c1 crab pell1234qrval eleq2d eqeq1 2rexbidv
        anbi1d elrab syl6bb ) DFGHIZCDUAJZICEKZAKZDUBJBKZLMUCMZNZUQOPMDUROPMLMU
        DMUENZQZBRSARSZETUFZICTICUSNZVAQZBRSARSZQUNUOVDCEABDUGUHVCVGECTUPCNZVBV
        FABRRVHUTVEVAUPCUSUIUKUJULUM $.
        $( [17-Sep-2014] $)

    $}

    $( [Characterize the full group of units as a set of nonzero reals closed under multiplication and division] $)

    $( General Pell solutions are (coded as) real numbers. $)
    pell1234qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> A
        e. RR ) $=
      ( va vb cn csquarenn cdif wcel cpell1234qr cfv wa cr cv cmul co wceq cexp
      c2 cz wrex csqr caddc cmin c1 elpell1234qr biimpd imp simpld ) BEFGHZABIJ
      HZKALHZACMZBUAJDMZNOUBOPULRQOBUMRQONOUCOUDPKDSTCSTZUIUJUKUNKZUIUJUOCDABUE
      UFUGUH $.
      $( [17-Sep-2014] $)

    $( No solution to a Pell equation is zero. $)
    pell1234qrne0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) ->
        A =/= 0 ) $=
      ( va vb cn wcel cc0 wne cmul co wceq c2 cexp cmin c1 wa cz cc syl syl2anc
      csquarenn cdif cpell1234qr cfv cr cv csqr caddc wrex elpell1234qr ax-1ne0
      simprl simpl eldifi nncn 3syl ad3antrrr sqrcl zcn ad2antll ad2antrr sqmul
      sqrth oveq1d eqtr2d oveq2d ad2antrl mulcl subsq eqtrd simpr subcl 3eqtr3d
      simplr mul02 ex necon3d mpi adantrl eqnetrd rexlimdvva expimpd sylbid imp
      ) BEUAUBFZABUCUDFZAGHZWEWFAUEFZACUFZBUGUDZDUFZIJZUHJZKZWILMJZBWKLMJZIJZNJ
      ZOKZPZDQUICQUIZPWGCDABUJWEWHXAWGWEWHPZWTWGCDQQXBWIQFZWKQFZPZPZWTWGXFWTPAW
      MGXFWNWSULXFWSWMGHZWNXFWSPZOGHXGUKXHWMGOGXHWMGKZOGKXHXIPZWRWMWIWLNJZIJZOG
      XJWRWOWLLMJZNJZXLXJWQXMWONXJXMWJLMJZWPIJZWQXJWJRFZWKRFZXMXPKXJBRFZXQXBXSX
      EWSXIXBWEBEFXSWEWHUMBEUAUNBUOUPUQZBURSZXFXRWSXIXDXRXBXCWKUSUTVAZWJWKVBTXJ
      XOBWPIXJXSXOBKXTBVCSVDVEVFXJWIRFZWLRFZXNXLKXFYCWSXIXCYCXBXDWIUSVGVAZXJXQX
      RYDYAYBWJWKVHTZWIWLVITVJXFWSXIVNXJXLGXKIJZGXJWMGXKIXHXIVKVDXJXKRFZYGGKXJY
      CYDYHYEYFWIWLVLTXKVOSVJVMVPVQVRVSVTVPWAWBWCWD $.
      $( [17-Sep-2014] $)

    $( General solutions of the Pell equation are closed under reciprocals. $)
    pell1234qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) )
        -> ( 1 / A ) e. ( Pell1234QR ` D ) ) $=
      ( vc vd va wcel wa c1 co cmul caddc wceq c2 cexp cz syl2anc syl cc oveq2d
      cmin vb cn csquarenn cdif cpell1234qr cdiv cr cv csqr elpell1234qr biimpd
      cfv wrex imp cc0 pell1234qrre pell1234qrne0 rereccl ad2antrr cneg simplrl
      wne simplrr znegcl eldifi nncn ad3antrrr sqrth oveq1d sqrcl eqcomd eqtr3d
      zcn sqmul simprr adantr ad2antlr mulcl subsq 3eqtr3d recid simprl mulneg2
      negsub eqtrd oveq12d 3eqtr4d negcl addcl mulcan syl112anc mpbid sqneg jca
      recn wb weq oveq1 eqeq2d eqeq1d anbi12d oveq2 rcla42ev syl3anc rexlimdvva
      ex adantld mpd mpbird ) BUBUCUDFZABUEULZFZGZHAUFIZXKFZXNUGFZXNCUHZBUIULZD
      UHZJIZKIZLZXQMNIZBXSMNIZJIZTIZHLZGZDOUMCOUMZGZXMAUGFZAEUHZXRUAUHZJIZKIZLZ
      YLMNIZBYMMNIZJIZTIZHLZGZUAOUMEOUMZGZYJXJXLUUDXJXLUUDEUAABUJUKUNXMUUCYJYKX
      MUUBYJEUAOOXMYLOFZYMOFZGZGZUUBYJUUHUUBGZXPYIXMXPUUGUUBXMYKAUOVBZXPABUPZAB
      UQZAURPZUSUUIUUEYMUTZOFZXNYLXRUUNJIZKIZLZYQBUUNMNIZJIZTIZHLZGZYIXMUUEUUFU
      UBVAUUIUUFUUOXMUUEUUFUUBVCZYMVDQUUIUURUVBUUIAXNJIZAUUQJIZLZUURUUIHYOYLYNT
      IZJIZUVEUVFUUIYTYQYNMNIZTIZHUVIUUIYSUVJYQTUUIXRMNIZYRJIZYSUVJUUIUVLBYRJUU
      IBRFZUVLBLXJUVNXLUUGUUBXJBUBFUVNBUBUCVEBVFQVGZBVHQVIUUIUVJUVMUUIXRRFZYMRF
      ZUVJUVMLUUIUVNUVPUVOBVJQZUUIUUFUVQUVDYMVMQZXRYMVNPVKVLSUUHYPUUAVOZUUIYLRF
      ZYNRFZUVKUVILUUGUWAXMUUBUUEUWAUUFYLVMVPVQZUUIUVPUVQUWBUVRUVSXRYMVRPZYLYNV
      SPVTUUIARFZUUJUVEHLXMUWEUUGUUBXMYKUWEUUKAWOQUSZXMUUJUUGUUBUULUSZAWAPUUIAY
      OUUQUVHJUUHYPUUAWBUUIUUQYLYNUTZKIZUVHUUIUUPUWHYLKUUIUVPUVQUUPUWHLUVRUVSXR
      YMWCPSUUIUWAUWBUWIUVHLUWCUWDYLYNWDPWEWFWGUUIXNRFZUUQRFZUWEUUJUVGUURWPXMUW
      JUUGUUBXMXPUWJUUMXNWOQUSUUIUWAUUPRFZUWKUWCUUIUVPUUNRFZUWLUVRUUIUVQUWMUVSY
      MWHQXRUUNVRPYLUUPWIPUWFUWGXNUUQAWJWKWLUUIUVAYTHUUIUUTYSYQTUUIUUSYRBJUUIUV
      QUUSYRLUVSYMWMQSSUVTWEWNYHUVCXNYLXTKIZLZYQYETIZHLZGCDYLUUNOOCEWQZYBUWOYGU
      WQUWRYAUWNXNXQYLXTKWRWSUWRYFUWPHUWRYCYQYETXQYLMNWRVIWTXAXSUUNLZUWOUURUWQU
      VBUWSUWNUUQXNUWSXTUUPYLKXSUUNXRJXBSWSUWSUWPUVAHUWSYEUUTYQTUWSYDUUSBJXSUUN
      MNWRSSWTXAXCXDWNXFXEXGXHXJXOYJWPXLCDXNBUJVPXI $.
      $( [18-Sep-2014] $)

    $( General solutions of the Pell equation are closed under
       multiplication. $)
    pell1234qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) /\
        B e. ( Pell1234QR ` D ) ) -> ( A x. B ) e. ( Pell1234QR ` D ) ) $=
      ( wcel cmul co wa caddc wceq c2 cexp cmin c1 cz ad3antrrr syl2anc oveq12d
      cc mulcl oveq2d va vb vc vd ve vf cn csquarenn cdif cpell1234qr cfv cr cv
      csqr wrex simplr remulcl syl simprl simplrl zmulcl simpll eldifi nnz 3syl
      wi simplrr simprr zaddcl ad2antrr zcn ad2antrl nncn sqrcl ad2antll adantr
      ad2antlr adantl muladd mul4 sqval sqrth eqtr3d oveq1d eqtrd mul12 syl3anc
      adddi eqcomd addcl sqmul subsq mulsub 3eqtrd subcl ax-1cn mulid2i a1i jca
      syl22anc oveq1 eqeq2d eqeq1d anbi12d oveq2 rcla42ev ex imp3a elpell1234qr
      rexlimdvva an4 syl6bb 3imtr4d exp3a 3imp ) CUGUHUIDZACUJUKZDZBXQDZABEFZXQ
      DZXPXRXSYAXPAULDZBULDZGZAUAUMZCUNUKZUBUMZEFZHFZIZYEJKFZCYGJKFZEFZLFZMIZGZ
      UBNUOUANUOZBUCUMZYFUDUMZEFZHFZIZYRJKFZCYSJKFZEFZLFZMIZGZUDNUOUCNUOZGZGZXT
      ULDZXTUEUMZYFUFUMZEFZHFZIZUUMJKFZCUUNJKFZEFZLFZMIZGZUFNUOUENUOZGZXRXSGZYA
      XPYDUUJUVEXPYDUUJUVEVFXPYDGZYQUUIUVEUVGYPUUIUVEVFZUAUBNNUVGYENDZYGNDZGZGZ
      YPUVHUVLYPGZUUHUVEUCUDNNUVMYRNDZYSNDZGZGZUUHUVEUVQUUHGZUULUVDUVRYDUULUVLY
      DYPUVPUUHXPYDUVKUPOABUQURUVRYEYREFZCYSYGEFZEFZHFZNDZYEYSEFZYRYGEFZHFZNDZX
      TUWBYFUWFEFZHFZIZUWBJKFZCUWFJKFZEFZLFZMIZGZUVDUVRUVSNDZUWANDZUWCUVRUVIUVN
      UWQUVLUVIYPUVPUUHUVGUVIUVJUSOZUVMUVNUVOUUHUTZYEYRVAPUVRCNDZUVTNDZUWRUVLUX
      AYPUVPUUHUVLXPCUGDZUXAXPYDUVKVBZCUGUHVCZCVDVEOUVRUVOUVJUXBUVMUVNUVOUUHVGZ
      UVLUVJYPUVPUUHUVGUVIUVJVHOZYSYGVAPCUVTVAPUVSUWAVIPUVRUWDNDZUWENDZUWGUVRUV
      IUVOUXHUWSUXFYEYSVAPUVRUVNUVJUXIUWTUXGYRYGVAPUWDUWEVIPUVRUWJUWOUVRXTYIUUA
      EFZUWIUVRAYIBUUAEUVMYJUVPUUHUVLYJYOUSVJUVQUUBUUGUSQUVRUXJUVSYTYHEFZHFZYEY
      TEFZYRYHEFZHFZHFZUWIUVRYERDZYHRDZYRRDZYTRDZUXJUXPIUVLUXQYPUVPUUHUVIUXQUVG
      UVJYEVKVLOZUVRYFRDZYGRDZUXRUVRCRDZUYBUVLUYDYPUVPUUHUVLXPUXCUYDUXDUXECVMVE
      OZCVNURZUVLUYCYPUVPUUHUVJUYCUVGUVIYGVKVOOZYFYGSPZUVPUXSUVMUUHUVNUXSUVOYRV
      KVPVQZUVRUYBYSRDZUXTUYFUVPUYJUVMUUHUVOUYJUVNYSVKVRVQZYFYSSPZYEYHYRYTVSWTU
      VRUXLUWBUXOUWHHUVRUXKUWAUVSHUVRUXKYFYFEFZUVTEFZUWAUVRUYBUYJUYBUYCUXKUYNIU
      YFUYKUYFUYGYFYSYFYGVTWTUVRUYMCUVTEUVRYFJKFZUYMCUVRUYBUYOUYMIUYFYFWAURUVRU
      YDUYOCIUYECWBURZWCWDWETZUVRUXOYFUWDEFZYFUWEEFZHFZUWHUVRUXMUYRUXNUYSHUVRUX
      QUYBUYJUXMUYRIUYAUYFUYKYEYFYSWFWGUVRUXSUYBUYCUXNUYSIUYIUYFUYGYRYFYGWFWGQU
      VRUWHUYTUVRUYBUWDRDZUWERDZUWHUYTIUYFUVRUXQUYJVUAUYAUYKYEYSSPZUVRUXSUYCVUB
      UYIUYGYRYGSPZYFUWDUWEWHWGWIWEZQWEZWEUVRUWNUXJYEYHLFZYRYTLFZEFZEFZYKUYOYLE
      FZLFZUUCUYOUUDEFZLFZEFZMUVRUWNUWKUWHJKFZLFZUWIUWBUWHLFZEFZVUJUVRUWMVUPUWK
      LUVRVUPUWMUVRVUPUYOUWLEFZUWMUVRUYBUWFRDZVUPVUTIUYFUVRVUAVUBVVAVUCVUDUWDUW
      EWJPZYFUWFWKPUVRUYOCUWLEUYPWDWEWITUVRUWBRDZUWHRDZVUQVUSIUVRUVSRDZUWARDZVV
      CUVRUXQUXSVVEUYAUYIYEYRSPUVRUYDUVTRDZVVFUYEUVRUYJUYCVVGUYKUYGYSYGSPCUVTSP
      UVSUWAWJPUVRUYBVVAVVDUYFVVBYFUWFSPUWBUWHWLPUVRUWIUXJVURVUIEUVRUXJUWIVUFWI
      UVRVUIVURUVRVUIUXLUXOLFZVURUVRUXQUXRUXSUXTVUIVVHIUYAUYHUYIUYLYEYHYRYTWMWT
      UVRUXLUWBUXOUWHLUYQVUEQWEWIQWNUVRVUJYIVUGEFZUUAVUHEFZEFZYKYHJKFZLFZUUCYTJ
      KFZLFZEFZVUOUVRYIRDZUUARDZVUGRDZVUHRDZVUJVVKIUVRUXQUXRVVQUYAUYHYEYHWJPUVR
      UXSUXTVVRUYIUYLYRYTWJPUVRUXQUXRVVSUYAUYHYEYHWOPUVRUXSUXTVVTUYIUYLYRYTWOPY
      IUUAVUGVUHVTWTUVRVVPVVKUVRVVMVVIVVOVVJEUVRUXQUXRVVMVVIIUYAUYHYEYHWLPUVRUX
      SUXTVVOVVJIUYIUYLYRYTWLPQWIUVRVVMVULVVOVUNEUVRVVLVUKYKLUVRUYBUYCVVLVUKIUY
      FUYGYFYGWKPTUVRVVNVUMUUCLUVRUYBUYJVVNVUMIUYFUYKYFYSWKPTQWNUVRVUOYNUUFEFMM
      EFZMUVRVULYNVUNUUFEUVRVUKYMYKLUVRUYOCYLEUYPWDTUVRVUMUUEUUCLUVRUYOCUUDEUYP
      WDTQUVRYNMUUFMEUVMYOUVPUUHUVLYJYOVHVJUVQUUBUUGVHQVWAMIUVRMWPWQWRWNWNWSUVC
      UWPXTUWBUUOHFZIZUWKUUTLFZMIZGUEUFUWBUWFNNUUMUWBIZUUQVWCUVBVWEVWFUUPVWBXTU
      UMUWBUUOHXAXBVWFUVAVWDMVWFUURUWKUUTLUUMUWBJKXAWDXCXDUUNUWFIZVWCUWJVWEUWOV
      WGVWBUWIXTVWGUUOUWHUWBHUUNUWFYFEXETXBVWGVWDUWNMVWGUUTUWMUWKLVWGUUSUWLCEUU
      NUWFJKXATTXCXDXFWGWSXGXJXGXJXHXGXHXPUVFYBYQGZYCUUIGZGUUKXPXRVWHXSVWIUAUBA
      CXIUCUDBCXIXDYBYQYCUUIXKXLUEUFXTCXIXMXNXO $.
      $( [18-Sep-2014] $)

    $( [Characterize the right branch Pell14 as the positive elements] $)

    $( A positive Pell solution is a general Pell solution. $)
    pell14qrss1234 $p |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) C_ (
        Pell1234QR ` D ) ) $=
      ( va vb vc cn csquarenn cdif wcel cpell14qr cv cmul co wceq c2 cexp wa cz
      cfv wrex cn0 cpell1234qr cr csqr caddc cmin c1 a1i anim1d reximdv2 anim2d
      wi nn0z elpell14qr elpell1234qr 3imtr4d ssrdv ) AEFGHZBAIRZAUARZUQBJZUBHZ
      UTCJZAUCRDJZKLUDLMVBNOLAVCNOLKLUELUFMPDQSZCTSZPVAVDCQSZPUTURHUTUSHUQVEVFV
      AUQVDVDCTQUQVBTHZVBQHZVDVGVHUKUQVBULUGUHUIUJCDUTAUMCDUTAUNUOUP $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a real number. $)
    pell14qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR ) $=
      ( cn csquarenn cdif wcel cpell14qr wa cpell1234qr cr simpl pell14qrss1234
      cfv sseld imp pell1234qrre syl2anc ) BCDEFZABGMZFZHRABIMZFZAJFRTKRTUBRSUA
      ABLNOABPQ $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a nonzero number. $)
    pell14qrne0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A
        =/= 0 ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpell1234qr cc0 wne pell14qrss1234
      wa simpl sselda pell1234qrne0 syl2anc ) BCDEFZABGHZFZMRABIHZFAJKRTNRSUAAB
      LOABPQ $.
      $( [17-Sep-2014] $)

    $( A positive Pell solution is a positive number. $)
    pell14qrgt0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> 0 <
        A ) $=
      ( va vb wcel cfv cc0 clt wbr cr cmul co wceq c2 cexp syl syl2anc ad2antlr
      wa cc cn csquarenn cdif cpell14qr cv csqr caddc cmin c1 cz cn0 elpell14qr
      wrex cabs 0cn a1i cle simplll eldifi nnre nnnn0 nn0ge0 resqrcl zre adantl
      remulcl abssub subid1 fveq2d eqtrd absresq sqrcl recnd sqmul sqrth oveq1d
      3syl recn 3eqtrd lt01 simpr breqtrrd wb resqcl nn0re adantr posdif mpbird
      eqbrtrd abscl absge0 lt2sq syl22anc 0re syl3anc mpbid simprd nn0cn addcom
      absdiflt adantrl simprl ex rexlimdvva expimpd sylbid imp ) BUAUBUCEZABUDF
      EZGAHIZXHXIAJEZACUEZBUFFZDUEZKLZUGLZMZXLNOLZBXNNOLZKLZUHLZUIMZSZDUJUMCUKU
      MZSXJCDABULXHXKYDXJXHXKSZYCXJCDUKUJYEXLUKEZXNUJEZSZSZYCXJYIYCSGXPAHYIYBGX
      PHIXQYIYBSZGXOXLUGLZXPHYJXOXLUHLGHIZGYKHIZYJGXOUHLUNFZXLHIZYLYMSZYJYNXOUN
      FZXLHYJYNXOGUHLZUNFZYQYJGTEZXOTEZYNYSMYTYJUOUPYJXOJEZUUAYJXMJEZXNJEZUUBYJ
      BJEZGBUQIZUUCYJBUAEZUUEYJXHUUGXHXKYHYBURBUAUBUSPZBUTPZYJUUGBUKEUUFUUHBVAB
      VBVQBVCQYHUUDYEYBYGUUDYFXNVDVEZRZXMXNVFQZXOVRPZGXOVGQYJYRXOUNYJUUAYRXOMUU
      MXOVHPVIVJYJYQXLHIZYQNOLZXRHIZYJUUOXTXRHYJUUOXONOLZXMNOLZXSKLZXTYJUUBUUOU
      UQMUULXOVKPYJXMTEZXNTEZUUQUUSMYJBTEZUUTYJUUEUVBUUIBVRPZBVLPYHUVAYEYBYHXNU
      UJVMRXMXNVNQYJUURBXSKYJUVBUURBMUVCBVOPVPVSYJXTXRHIZGYAHIZYJGUIYAHGUIHIYJV
      TUPYIYBWAWBYJXTJEZXRJEZUVDUVEWCYJUUEXSJEZUVFUUIYJUUDUVHUUKXNWDPBXSVFQYJXL
      JEZUVGYHUVIYEYBYFUVIYGXLWEWFRZXLWDPXTXRWGQWHWIYJYQJEZGYQUQIZUVIGXLUQIZUUN
      UUPWCYJUUAUVKUUMXOWJPYJUUAUVLUUMXOWKPUVJYHUVMYEYBYFUVMYGXLVBWFRYQXLWLWMWH
      WIYJGJEZUUBUVIYOYPWCUVNYJWNUPUULUVJGXOXLWTWOWPWQYJXLTEZUUAXPYKMYHUVOYEYBY
      FUVOYGXLWRWFRUUMXLXOWSQWBXAYIXQYBXBWBXCXDXEXFXG $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a positive real. $)
    pell14qrrp $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR+ ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cc0 clt wbr pell14qrre pell14qrgt0
      wa cr crp elrp sylanbrc ) BCDEFABGHFNAOFIAJKAPFABLABMAQR $.
      $( [19-Sep-2014] $)

    $( A general Pell solution is either a positive solution, or its negation
       is. $)
    pell1234qrdich $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) ->
        ( A e. ( Pell14QR ` D ) \/ -u A e. ( Pell14QR ` D ) ) ) $=
      ( va vb vc wcel cneg cmul co caddc wceq c2 cexp cmin c1 wa wrex cn0 syl
      cz vd cn csquarenn cdif cpell1234qr cfv cpell14qr wo cr csqr elpell1234qr
      cv wi elznn0 biimpi simprd adantl simplr ad2antrr simpr weq eqidd eqeq12d
      oveq1 oveq123d eqeq1d anbi12d rexbidv rcla4ev jca wb elpell14qr ad3antrrr
      syl2anc adantr mpbird orcd ex renegcl simpllr znegcl simprl negeqd cc zcn
      eldifi nncn sqrcl ad2antlr mulcl negdi mulneg2 eqcomd oveq2d 3eqtrd sqneg
      oveq12d simprr eqtrd eqeq2d oveq1d oveq2 rcla42ev olcd rexlimdva jaod mpd
      syl3anc expimpd sylbid imp ) BUBUCUDFZABUEUFFZABUGUFZFZAGZXNFZUHZXLXMAUIF
      ZACULZBUJUFZDULZHIZJIZKZXTLMIZBYBLMIZHIZNIZOKZPZDTQZCTQZPXRCDABUKXLXSYMXR
      XLXSPZYLXRCTYNXTTFZPZXTRFZXTGZRFZUHZYLXRUMZYOYTYNYOXTUIFZYTYOUUBYTPXTUNUO
      UPUQYPYQUUAYSYPYQUUAYPYQPZYLXRUUCYLPZXOXQUUDXOXSAEULZYCJIZKZUUELMIZYHNIZO
      KZPZDTQZERQZPZUUDXSUUMYPXSYQYLXLXSYOURZUSUUDYQYLUUMYPYQYLURUUCYLUTUULYLEX
      TRECVAZUUKYKDTUUPUUGYEUUJYJUUPAAUUFYDUUPAVBUUEXTYCJVDVCUUPUUIYIOUUPUUHYFY
      HYHNNUUPNVBUUEXTLMVDUUPYHVBVEVFVGVHVIVNVJYNXOUUNVKZYOYQYLXLUUQXSEDABVLVOV
      MVPVQVRVRYPYSUUAYPYSPZYKXRDTUURYBTFZPZYKXRUUTYKPZXQXOUVAXQXPUIFZXPUUEYAUA
      ULZHIZJIZKZUUHBUVCLMIZHIZNIZOKZPZUATQERQZPZUVAUVBUVLUVAXSUVBYPXSYSUUSYKUU
      OVMAVSSUVAYSYBGZTFZXPYRYAUVNHIZJIZKZYRLMIZBUVNLMIZHIZNIZOKZPZUVLYPYSUUSYK
      VTUVAUUSUVOUURUUSYKURYBWASUVAUVRUWCUVAXPYDGZYRYCGZJIZUVQUVAAYDUUTYEYJWBWC
      UVAXTWDFZYCWDFZUWEUWGKYPUWHYSUUSYKYOUWHYNXTWEUQVMZUVAYAWDFZYBWDFZUWIUVABW
      DFZUWKYPUWMYSUUSYKXLUWMXSYOXLBUBFUWMBUBUCWFBWGSUSVMBWHSZUUSUWLUURYKYBWEWI
      ZYAYBWJVNXTYCWKVNUVAUWFUVPYRJUVAUWKUWLUWFUVPKUWNUWOUWKUWLPUVPUWFYAYBWLWMV
      NWNWOUVAUWBYIOUVAUVSYFUWAYHNUVAUWHUVSYFKUWJXTWPSUVAUVTYGBHUVAUWLUVTYGKUWO
      YBWPSWNWQUUTYEYJWRWSVJUVKUWDXPYRUVDJIZKZUVSUVHNIZOKZPEUAYRUVNRTUUEYRKZUVF
      UWQUVJUWSUWTUVEUWPXPUUEYRUVDJVDWTUWTUVIUWROUWTUUHUVSUVHNUUEYRLMVDXAVFVGUV
      CUVNKZUWQUVRUWSUWCUXAUWPUVQXPUXAUVDUVPYRJUVCUVNYAHXBWNWTUXAUWRUWBOUXAUVHU
      WAUVSNUXAUVGUVTBHUVCUVNLMVDWNWNVFVGXCXHVJYPXQUVMVKZYSUUSYKXLUXBXSYOEUAXPB
      VLUSVMVPXDVRXEVRXFXGXEXIXJXK $.
      $( [18-Sep-2014] $)

    $( A number is a positive Pell solution iff it is positive and a Pell
       solution, justifying our name choice. $)
    elpell14qr2 $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A
        e. ( Pell1234QR ` D ) /\ 0 < A ) ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpell1234qr cc0 clt pell14qrss1234
      wbr wa sselda pell14qrgt0 wn cr wi adantrr jca wo 0re pell1234qrre ltnsym
      cneg sylancr impr wb lt0neg1 syl mtbid ex adantr mtod pell1234qrdich sylc
      orel2 impbida ) BCDEFZABGHZFZABIHZFZJAKMZNZUTVBNVDVEUTVAVCABLOABPUAUTVFNZ
      AUFZVAFZQVBVIUBZVBVGVIJVHKMZVGAJKMZVKUTVDVEVLQZUTVDNJRFARFZVEVMSUCABUDZJA
      UEUGUHVGVNVLVKUIUTVDVNVEVOTAUJUKULUTVIVKSVFUTVIVKVHBPUMUNUOUTVDVJVEABUPTV
      IVBURUQUS $.
      $( [19-Oct-2014] $)

    $( Positive Pell solutions are closed under multiplication. $)
    pell14qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ( Pell14QR ` D ) ) -> ( A x. B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cmul co cpell1234qr cc0 clt wbr wa
      cr pell1234qrre syl2anc elpell14qr2 simpl simprll simprrl pell1234qrmulcl
      syl3anc simprlr simprrr mulgt0 syl22anc jca ex anbi12d 3imtr4d exp3a 3imp
      ) CDEFGZACHIZGZBUQGZABJKZUQGZUPURUSVAUPACLIZGZMANOZPZBVBGZMBNOZPZPZUTVBGZ
      MUTNOZPZURUSPVAUPVIVLUPVIPZVJVKVMUPVCVFVJUPVIUAZUPVCVDVHUBZUPVEVFVGUCZABC
      UDUEVMAQGZVDBQGZVGVKVMUPVCVQVNVOACRSUPVCVDVHUFVMUPVFVRVNVPBCRSUPVEVFVGUGA
      BUHUIUJUKUPURVEUSVHACTBCTULUTCTUMUNUO $.
      $( [17-Sep-2014] $)

    $( Positive Pell solutions are closed under reciprocal. $)
    pell14qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> (
        1 / A ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv c1 cdiv co cpell1234qr cc0 clt wbr
      wa pell1234qrreccl adantrr cr elpell14qr2 pell1234qrre simprr syl2anc jca
      recgt0 ex 3imtr4d imp ) BCDEFZABGHZFZIAJKZUJFZUIABLHZFZMANOZPZULUNFZMULNO
      ZPZUKUMUIUQUTUIUQPZURUSUIUOURUPABQRVAASFZUPUSUIUOVBUPABUARUIUOUPUBAUEUCUD
      UFABTULBTUGUH $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are closed under division. $)
    pell14qrdivcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ( Pell14QR ` D ) ) -> ( A / B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv w3a cdiv co c1 cmul cc0 pell14qrre
      cc wa recnd 3adant2 wceq 3adant3 pell14qrne0 divrec syl3anc pell14qrreccl
      wne pell14qrmulcl syld3an3 eqeltrd ) CDEFGZACHIZGZBULGZJZABKLZAMBKLZNLZUL
      UOAQGZBQGZBOUGZUPURUAUKUMUSUNUKUMRAACPSUBUKUNUTUMUKUNRBBCPSTUKUNVAUMBCUCT
      ABUDUEUKUMUNUQULGZURULGUKUNVBUMBCUFTAUQCUHUIUJ $.
      $( [18-Sep-2014] $)

    $( Lemma for ~ pell14qrexpcl . $)
    pell14qrexpclnn0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B
        e. NN0 ) -> ( A ^ B ) e. ( Pell14QR ` D ) ) $=
      ( va vb cn wcel cn0 cexp co cv wi cc0 c1 wceq oveq2 eleq1d imbi2d syl2anc
      eqeltrd csquarenn cdif cpell14qr cfv wa caddc weq cdiv cc pell14qrre exp0
      recnd syl wne pell14qrne0 eqtr4d pell14qrdivcl 3anidm23 w3a cmul 3ad2ant2
      divid simp1 expp1 simp2l simp2r pell14qrmulcl syl3anc 3exp a2d exp3acom3r
      simp3 nn0ind 3imp ) CFUAUBGZACUCUDZGZBHGZABIJZVPGZVRVOVQVTVOVQUEZADKZIJZV
      PGZLWAAMIJZVPGZLWAAEKZIJZVPGZLWAAWGNUFJZIJZVPGZLWAVTLDEBWBMOZWDWFWAWMWCWE
      VPWBMAIPQRDEUGZWDWIWAWNWCWHVPWBWGAIPQRWBWJOZWDWLWAWOWCWKVPWBWJAIPQRWBBOZW
      DVTWAWPWCVSVPWBBAIPQRWAWEAAUHJZVPWAWENWQWAAUIGZWENOWAAACUJULZAUKUMWAWRAMU
      NWQNOWSACUOAVBSUPVOVQWQVPGAACUQURTWGHGZWAWIWLWTWAWIWLWTWAWIUSZWKWHAUTJZVP
      XAWRWTWKXBOWAWTWRWIWSVAWTWAWIVCAWGVDSXAVOWIVQXBVPGWTVOVQWIVEWTWAWIVLWTVOV
      QWIVFWHACVGVHTVIVJVMVKVN $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are closed under integer powers. $)
    pell14qrexpcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ZZ ) -> ( A ^ B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv co cn0 wa simplll pell14qrexpclnn0
      cexp simpllr simpr syl3anc cc recnd cz cr cneg wo c1 cdiv wceq pell14qrre
      elznn0 ad2antrr simplr expneg2 pell14qrreccl syl2anc jaodan syl5bi 3impia
      eqeltrd expl ) CDEFGZACHIZGZBUAGZABOJZVAGZVCBUBGZBKGZBUCZKGZUDZLUTVBLZVEB
      UIVKVFVJVEVKVFLZVGVEVIVLVGLUTVBVGVEUTVBVFVGMUTVBVFVGPVLVGQABCNRVLVILZVDUE
      AVHOJZUFJZVAVMASGZBSGVIVDVOUGVKVPVFVIVKAACUHTUJVMBVKVFVIUKTVLVIQZABULRVMU
      TVNVAGZVOVAGUTVBVFVIMZVMUTVBVIVRVSUTVBVFVIPVQAVHCNRVNCUMUNURUOUSUPUQ $.
      $( [Characterize the first quadrant Pell1 as the elements ge 1] $)

    $( First-quadrant Pell solutions are a subset of the positive solutions. $)
    pell1qrss14 $p |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) C_ ( Pell14QR ` D
        ) ) $=
      ( va vc vb cn csquarenn cdif wcel cpell1qr cfv cv cmul co wceq c2 cexp wa
      cn0 wrex cz cpell14qr cr csqr caddc cmin nn0z a1i anim1d reximdv2 reximdv
      c1 wi anim2d elpell1qr elpell14qr 3imtr4d ssrdv ) AEFGHZBAIJZAUAJZURBKZUB
      HZVACKZAUCJDKZLMUDMNVCOPMAVDOPMLMUEMUKNQZDRSZCRSZQVBVEDTSZCRSZQVAUSHVAUTH
      URVGVIVBURVFVHCRURVEVEDRTURVDRHZVDTHZVEVJVKULURVDUFUGUHUIUJUMCDVAAUNCDVAA
      UOUPUQ $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is either in the first quadrant, or its
       reciprocal is. $)
    pell14qrdich $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> ( A
        e. ( Pell1QR ` D ) \/ ( 1 / A ) e. ( Pell1QR ` D ) ) ) $=
      ( va vb wcel wa cmul co caddc wceq cexp cmin cn0 adantr ad3antrrr syl2anc
      c2 c1 cc oveq2d vc cn csquarenn cdif cpell14qr cfv cr cv csqr cz cpell1qr
      wrex cdiv wo elpell14qr biimpa cneg simplrr elznn0 simprd simplr ad2antrr
      sylib simprl simpr ra42e syl3anc jca ex elpell1qr sylibrd cc0 pell14qrne0
      wb wne simpll rereccl pell14qrre recnd recid simprr nn0cn ad2antrl eldifi
      nncn syl sqrcl zcn ad2antll mulcl subsq sqmul sqrth oveq1d eqtr2d mulneg2
      negsub eqcomd oveq12d 3eqtr4d adantrr 3eqtr2d reccl negcl addcl syl112anc
      eqtr4d mulcan mpbid sqneg eqtrd oveq2 eqeq2d oveq1 eqeq1d anbi12d rcla4ev
      ra4e orim12d mpd rexlimdvva expimpd ) BUBUCUDEZABUEUFEZFZAUGEZACUHZBUIUFZ
      DUHZGHZIHZJZYGQKHZBYIQKHZGHZLHZRJZFZDUJULCMULZFZABUKUFZEZRAUMHZUUAEZUNZYC
      YDYTCDABUOUPYEYFYSUUEYEYFFZYRUUECDMUJUUFYGMEZYIUJEZFZFZYRUUEUUJYRFZYIMEZY
      IUQZMEZUNZUUEUUKYIUGEZUUOUUKUUHUUPUUOFUUFUUGUUHYRURYIUSVCUTUUKUULUUBUUNUU
      DUUKUULYFYRDMULCMULZFZUUBUUKUULUURUUKUULFZYFUUQUUJYFYRUULYEYFUUIVAZVBUUSU
      UGUULYRUUQUUJUUGYRUULUUFUUGUUHVDZVBUUKUULVEUUJYRUULVAYRCDMMVFVGVHVIYEUUBU
      URVNZYFUUIYRYCUVBYDCDABVJNOVKUUKUUNUUCUGEZUUCYGYHUAUHZGHZIHZJZYMBUVDQKHZG
      HZLHZRJZFZUAMULZCMULZFZUUDUUKUUNUVOUUKUUNFZUVCUVNUVPYFAVLVOZUVCUUJYFYRUUN
      UUTVBUVPYCYDUVQUUFYCUUIYRUUNYCYDYFVPOUUFYDUUIYRUUNYCYDYFVAOABVMZPAVQPUVPU
      UGUVMUVNUUJUUGYRUUNUVAVBUVPUUNUUCYGYHUUMGHZIHZJZYMBUUMQKHZGHZLHZRJZFZUVMU
      UKUUNVEUVPUWAUWEUUKUWAUUNUUKAUUCGHZAUVTGHZJZUWAUUKUWGRYPUWHYEUWGRJZYFUUIY
      RYEASEZUVQUWJYEAABVRVSZUVRAVTPOUUJYLYQWAUUJYLYPUWHJYQUUJYLFZYMYJQKHZLHZYK
      YGYJLHZGHZYPUWHUWMYGSEZYJSEZUWOUWQJUUJUWRYLUUGUWRUUFUUHYGWBWCZNUUJUWSYLUU
      JYHSEZYISEZUWSUUJBSEZUXAYCUXCYDYFUUIYCBUBEUXCBUBUCWDBWEWFOZBWGWFZUUHUXBUU
      FUUGYIWHWIZYHYIWJPZNYGYJWKPUUJYPUWOJYLUUJYOUWNYMLUUJUWNYHQKHZYNGHZYOUUJUX
      AUXBUWNUXIJUXEUXFYHYIWLPUUJUXHBYNGUUJUXCUXHBJUXDBWMWFWNWOTNUWMAYKUVTUWPGU
      UJYLVEUUJUVTUWPJYLUUJUVTYGYJUQZIHZUWPUUJUVSUXJYGIUUJUXAUXBUVSUXJJUXEUXFYH
      YIWPPTUUJUWRUWSUWPUXKJUWTUXGUWRUWSFUXKUWPYGYJWQWRPXGNWSWTXAXBUUKUUCSEZUVT
      SEZUWKUVQUWIUWAVNYEUXLYFUUIYRYEUWKUVQUXLUWLUVRAXCPOUUJUXMYRUUJUWRUVSSEZUX
      MUWTUUJUXAUUMSEZUXNUXEUUJUXBUXOUXFYIXDWFYHUUMWJPYGUVSXEPNYEUWKYFUUIYRUWLO
      YEUVQYFUUIYRUVROUUCUVTAXHXFXINUVPUWDYPRUVPUWCYOYMLUVPUWBYNBGUVPUXBUWBYNJU
      UJUXBYRUUNUXFVBYIXJWFTTUUJYLYQUUNURXKVHUVLUWFUAUUMMUVDUUMJZUVGUWAUVKUWEUX
      PUVFUVTUUCUXPUVEUVSYGIUVDUUMYHGXLTXMUXPUVJUWDRUXPUVIUWCYMLUXPUVHUWBBGUVDU
      UMQKXNTTXOXPXQPUVMCMXRPVHVIYEUUDUVOVNZYFUUIYRYCUXQYDCUAUUCBVJNOVKXSXTVIYA
      YBXT $.
      $( [18-Sep-2014] $)

    $( A Pell solution in the first quadrant is at least 1. $)
    pell1qrge1 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) ) -> 1 <_ A
        ) $=
      ( va vb wcel c1 cle wbr cr co wceq c2 wa cn0 a1i nn0re syl cc0 syl2anc cc
      cn csquarenn cdif cpell1qr cfv cv csqr cmul caddc cexp cmin elpell1qr 1re
      wrex simplrl simplll eldifi nnnn0 nn0ge0 resqrcl simplrr remulcl nn0expcl
      3syl readdcl 2nn0 nn0mulcl wb addge02 mpbid sq1 ad2antrl sqcl simpll nncn
      nn0cn ad2antll mulcl ax-1cn subadd syl3anc biimpa eqcomd 3brtr4d syl22anc
      1nn0 nn0ge0i le2sq mpbird sqrge0 mulge0 addge01 letrd adantrl breqtrrd ex
      simprl rexlimdvva expimpd sylbid imp ) BUAUBUCEZABUDUEEZFAGHZXBXCAIEZACUF
      ZBUGUEZDUFZUHJZUIJZKZXFLUJJZBXHLUJJZUHJZUKJFKZMZDNUNCNUNZMXDCDABULXBXEXQX
      DXBXEMZXPXDCDNNXRXFNEZXHNEZMZMZXPXDYBXPMFXJAGYBXOFXJGHXKYBXOMZFXFXJFIEZYC
      UMOZYCXSXFIEZXRXSXTXOUOZXFPQZYCYFXIIEZXJIEYHYCXGIEZXHIEZYIYCBIEZRBGHZYJYC
      BNEZYLYCXBBUAEZYNXBXEYAXOUPBUAUBUQZBURVDZBPQZYCYNYMYQBUSQZBUTSZYCXTYKXRXS
      XTXOVAZXHPQZXGXHVBSZXFXIVESYCFXFGHZFLUJJZXLGHZYCFXNFUIJZUUEXLGYCRXNGHZFUU
      GGHZYCXNNEZUUHYCYNXMNEZUUJYQYCXTLNEZUUKUUAUULYCVFOXHLVCSBXMVGSZXNUSQYCYDX
      NIEZUUHUUIVHYEYCUUJUUNUUMXNPQFXNVISVJUUEFKYCVKOYCUUGXLYBXOUUGXLKZYBXLTEZX
      NTEZFTEZXOUUOVHYBXFTEZUUPXSUUSXRXTXFVPVLXFVMQYBBTEZXMTEZUUQYBXBYOUUTXBXEY
      AVNYPBVOVDYBXHTEZUVAXTUVBXRXSXHVPVQXHVMQBXMVRSUURYBVSOXLXNFVTWAWBWCWDYCYD
      RFGHZYFRXFGHZUUDUUFVHYEUVCYCFWFWGOYHYCXSUVDYGXFUSQFXFWHWEWIYCRXIGHZXFXJGH
      ZYCYJRXGGHZYKRXHGHZUVEYTYCYLYMUVGYRYSBWJSUUBYCXTUVHUUAXHUSQXGXHWKWEYCYFYI
      UVEUVFVHYHUUCXFXIWLSVJWMWNYBXKXOWQWOWPWRWSWTXA $.
      $( [17-Sep-2014] $)

    $( 1 is a Pell solution and in the first quadrant as one. $)
    pell1qr1 $p |- ( D e. ( NN \ []NN ) -> 1 e. ( Pell1QR ` D ) ) $=
      ( va vb cn wcel c1 cmul co caddc wceq c2 cexp cmin cn0 a1i cc0 syl oveq2d
      wa oveq1 csquarenn cdif cpell1qr cfv cr csqr wrex elpell1qr 1re 1nn0 0nn0
      cv cc eldifi sqrcl mul01 ax-1cn addid1i syl6req sq1 oveq2i syl5eq oveq12d
      nncn subid1i syl6eq eqeq2d oveq1d eqeq1d anbi12d oveq2 rcla42ev syl112anc
      sq0 mpbir2and ) ADUAUBEZFAUCUDEFUEEZFBULZAUFUDZCULZGHZIHZJZVRKLHZAVTKLHZG
      HZMHZFJZSZCNUGBNUGZBCFAUHVQVPUIOVPFNEZPNEZFFVSPGHZIHZJZFKLHZAPKLHZGHZMHZF
      JZWJWKVPUJOWLVPUKOVPWNFPIHFVPWMPFIVPVSUMEZWMPJVPAUMEZXAVPADEXBADUAUNAVDQZ
      AUOQVSUPQRFUQURUSVPWSFPMHFVPWPFWRPMWPFJVPUTOVPWRAPGHZPWQPAGVNVAVPXBXDPJXC
      AUPQVBVCFUQVEVFWIWOWTSFFWAIHZJZWPWFMHZFJZSBCFPNNVRFJZWCXFWHXHXIWBXEFVRFWA
      ITVGXIWGXGFXIWDWPWFMVRFKLTVHVIVJVTPJZXFWOXHWTXJXEWNFXJWAWMFIVTPVSGVKRVGXJ
      XGWSFXJWFWRWPMXJWEWQAGVTPKLTRRVIVJVLVMVO $.
      $( [17-Sep-2014] $)

    $( The first quadrant solutions are precisely the positive Pell solutions
       which are at least one. $)
    elpell1qr2 $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e.
        ( Pell14QR ` D ) /\ 1 <_ A ) ) ) $=
      ( wcel cfv c1 cle wbr wa pell1qrge1 clt wceq wo cr wb 1re syl2anc cdiv co
      a1i adantr csquarenn cpell1qr cpell14qr pell1qrss14 sselda jca pell14qrre
      cn cdif leloe wn ltnle biimpa ax-1cn div1i eqcomi breq2d pell14qrgt0 lt01
      cc0 lerec2 syl22anc bitrd mtbid simplll simpr mtand pell14qrdich pell1qr1
      orel2 sylc ad2antrr eqeltrrd jaodan ex sylbid impr impbida ) BUHUAUICZABU
      BDZCZABUCDZCZEAFGZHVSWAHWCWDVSVTWBABUDUEABIUFVSWCWDWAVSWCHZWDEAJGZEAKZLZW
      AWEEMCZAMCZWDWHNWIWEOSZABUGZEAUJPWEWHWAWEWFWAWGWEWFHZEAQRZVTCZUKWAWOLZWAW
      MWOEWNFGZWMAEFGZWQWEWFWRUKZWEWIWJWFWSNWKWLEAULPUMWMWRAEEQRZFGZWQWMEWTAFEW
      TKWMWTEEUNUOUPSUQWMWJUTAJGZWIUTEJGZXAWQNWEWJWFWLTWEXBWFABURTWIWMOSXCWMUSS
      AEVAVBVCVDWMWOHVSWOWQVSWCWFWOVEWMWOVFWNBIPVGWEWPWFABVHTWOWAVJVKWEWGHEAVTW
      EWGVFVSEVTCWCWGBVIVLVMVNVOVPVQVR $.
      $( [18-Sep-2014] $)

    $( Lemma for ~ pell1qrgap . $)
    pell1qrgaplem $p |- ( ( ( D e. NN /\ ( A e. NN0 /\ B e. NN0 ) ) /\ ( 1 < (
        A + ( ( sqr ` D ) x. B ) ) /\ ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 )
        ) -> ( ( sqr ` ( D + 1 ) ) + ( sqr ` D ) ) <_ ( A + ( ( sqr ` D ) x. B
        ) ) ) $=
      ( wcel c1 cmul co caddc wbr cmin wceq cr a1i syl2anc syl cle cc cc0 mpbid
      wb cn cn0 wa csqr cfv clt cexp crp nnrp ad2antrr 1rp rpaddcl rpsqrcl rpre
      c2 readdcl nn0re adantl ad2antlr remulcl adantr rpcn mulid1 simplrr elnn0
      wo biimpi nnge1 wn simplrl oveq1 sq0 eqtrd oveq2d mul01 recnd sqcl subid1
      sq1 eqcomi 3eqtr3d nn0ge0 1nn0 nn0ge0i sq11 syl22anc simpr oveq12d ax-1cn
      1re addid1i breqtrd ltnri pm2.24 sylc jaodan mpdan rpgt0 lemul2 syl112anc
      eqbrtrrd leadd2 syl3anc le2sq resqcl suble0 mpbird 0re nngt0 sqrth simprr
      resubcl eqcomd mulcl subdi oveq1d eqtr2d 3eqtrd addid1 rpge0 leadd1 letrd
      addsub12 3brtr4d ) CUADZAUBDZBUBDZUCZUCZEACUDUEZBFGZHGZUFIZAUOUGGZCBUOUGG
      ZFGZJGZEKZUCZUCZCEHGZUDUEZYJHGZUUBYKHGZYLYTUUBLDZYJLDZUUCLDYTUUBUHDZUUEYT
      UUAUHDZUUGYTCUHDZEUHDZUUHYEUUIYHYSCUIUJZUUJYTUKMCEULNZUUAUMOZUUBUNOZYTYJU
      HDZUUFYTUUIUUOUUKCUMOZYJUNOZUUBYJUPNYTUUEYKLDZUUDLDUUNYTUUFBLDZUURUUQYHUU
      SYEYSYGUUSYFBUQURUSZYJBUTNZUUBYKUPNYTALDZUURYLLDYHUVBYEYSYFUVBYGAUQVAUSZU
      VAAYKUPNYTYJYKPIZUUCUUDPIZYTYJEFGZYJYKPYTYJQDZUVFYJKYTUUOUVGUUPYJVBOZYJVC
      OYTEBPIZUVFYKPIZYTBUADZBRKZVFZUVIYTYGUVMYEYFYGYSVDYGUVMBVEVGOYTUVKUVIUVLU
      VKUVIYTBVHURYTUVLUCZEEUFIZUVOVIZUVIUVNEYLEUFYIYMYRUVLVJUVNYLERHGZEUVNAEYK
      RHUVNYNEUOUGGZKZAEKZUVNYQEYNUVRYIYMYRUVLVDUVNYQYNRJGZYNUVNYPRYNJUVNYPCRFG
      ZRUVNYORCFUVNYORUOUGGZRUVLYOUWCKYTBRUOUGVKURUWCRKUVNVLMVMVNUVNCQDZUWBRKZY
      TUWDUVLYTUUIUWDUUKCVBOZVACVOZOVMVNUVNYNQDZUWAYNKYTUWHUVLYTAQDUWHYTAUVCVPA
      VQOZVAYNVROVMEUVRKUVNUVREVSVTMWAYTUVSUVTTZUVLYTUVBRAPIZELDZREPIZUWJUVCYHU
      WKYEYSYFUWKYGAWBVAUSZUWLYTWJMZUWMYTEWCWDMZAEWEWFVASUVNYKYJRFGZRUVNBRYJFYT
      UVLWGVNUVNUVGUWQRKYTUVGUVLUVHVAYJVOOVMWHUVQEKUVNEWIWKMVMWLUVPUVNEWJWMMUVO
      UVIWNWOWPWQZYTUWLUUSUUFRYJUFIZUVIUVJTUWOUUTUUQYTUUOUWSUUPYJWROEBYJWSWTSXA
      YTUUFUURUUEUVDUVETUUQUVAUUNYJYKUUBXBXCSYTUUBAPIZUUDYLPIZYTUWTUUBUOUGGZYNP
      IZYTYNCEYOJGZFGZHGZYNUWBHGZUXBYNPYTUXEUWBPIZUXFUXGPIZYTUXDRPIZUXHYTUXJEYO
      PIZYTUVREYOPUVREKYTVSMYTUVIUVRYOPIZUWRYTUWLUWMUUSRBPIZUVIUXLTUWOUWPUUTYHU
      XMYEYSYGUXMYFBWBURUSEBXDWFSXAYTUWLYOLDZUXJUXKTUWOYTUUSUXNUUTBXEOZEYOXFNXG
      YTUXDLDZRLDZCLDZRCUFIZUXJUXHTYTUWLUXNUXPUWOUXOEYOXLNZUXQYTXHMZYTUUIUXRUUK
      CUNOZYEUXSYHYSCXIUJUXDRCWSWTSYTUXELDZUWBLDZYNLDZUXHUXITYTUXRUXPUYCUYBUXTC
      UXDUTNYTUXRUXQUYDUYBUYACRUTNYTUVBUYEUVCAXEOUXEUWBYNXBXCSYTUXBUUACYQHGZUXF
      YTUUAQDZUXBUUAKYTUUHUYGUULUUAVBOUUAXJOYTEYQCHYTYQEYIYMYRXKXMVNYTUYFYNCYPJ
      GZHGZUXFYTUWDUWHYPQDZUYFUYIKUWFUWIYTUWDYOQDZUYJUWFYTBQDUYKYTBUUTVPBVQOZCY
      OXNNCYNYPYCXCYTUYHUXEYNHYTUXECEFGZYPJGZUYHYTUWDEQDUYKUXEUYNKUWFYTEUWOVPUY
      LCEYOXOXCYTUYMCYPJYTUWDUYMCKUWFCVCOXPXQVNVMXRYTUXGYNRHGZYNYTUWBRYNHYTUWDU
      WEUWFUWGOVNYTUWHUYOYNKUWIYNXSOXQYDYTUUERUUBPIZUVBUWKUWTUXCTUUNYTUUGUYPUUM
      UUBXTOUVCUWNUUBAXDWFXGYTUUEUVBUURUWTUXATUUNUVCUVAUUBAYKYAXCSYB $.
      $( [18-Sep-2014] $)

    $( First-quadrant Pell solutions are bounded away from 1.  (This particular
       bound allows us to prove exact values for the fundamental solution
       later.) $)
    pell1qrgap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) /\ 1 < A )
        -> ( ( sqr ` ( D + 1 ) ) + ( sqr ` D ) ) <_ A ) $=
      ( va vb cn csquarenn wcel cfv c1 clt wbr caddc co csqr cle wa cv cmul cn0
      wceq cdif cpell1qr wi cr cexp cmin wrex elpell1qr adantr eldifi ad3antrrr
      c2 simplr simpr simprl breqtrd pell1qrgaplem syl22anc breqtrrd rexlimdvva
      wb simprr ex expimpd sylbid com23 3imp ) BEFUAGZABUBHGZIAJKZBILMNHBNHZLMZ
      AOKZVHVJVIVMVHVJVIVMUCVHVJPZVIAUDGZACQZVKDQZRMLMZTZVPULUEMBVQULUEMRMUFMIT
      ZPZDSUGCSUGZPZVMVHVIWCVAVJCDABUHUIVNVOWBVMVNVOPZWAVMCDSSWDVPSGVQSGPZPZWAV
      MWFWAPZVLVRAOWGBEGZWEIVRJKVTVLVROKVNWHVOWEWAVHWHVJBEFUJUIUKWDWEWAUMWGIAVR
      JVNVJVOWEWAVHVJUNUKWFVSVTUOZUPWFVSVTVBVPVQBUQURWIUSVCUTVDVEVCVFVG $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are bounded away from 1. $)
    pell14qrgap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> ( ( sqr ` ( D + 1 ) ) + ( sqr ` D ) ) <_ A ) $=
      ( cn csquarenn cdif wcel cpell1qr cfv cpell14qr c1 clt wbr caddc csqr cle
      co w3a wa wb cr elpell1qr2 3ad2ant1 wi 1re pell14qrre ltle sylancr 3impia
      simp2 mpbir2and pell1qrgap syld3an2 ) BCDEFZABGHFZABIHFZJAKLZBJMPNHBNHMPA
      OLUMUOUPQUNUOJAOLZUMUOUNUOUQRSUPABUAUBUMUOUPUIUMUOUPUQUMUORJTFATFUPUQUCUD
      ABUEJAUFUGUHUJABUKUL $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are bounded away from 1, with a friendlier
       bound. $)
    pell14qrgapw $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> 2 < A ) $=
      ( cn wcel cfv c1 clt wbr c2 caddc co cr a1i crp syl wceq 1re cexp cle wb
      csquarenn cdif cpell14qr w3a csqr 2re eldifi 3ad2ant1 1rp rpaddcl syl2anc
      nnrp rpsqrcl rpre readdcl pell14qrre 3adant3 df-2 readdcli peano2re nnge1
      nnre ltp1 lelttrd sq1 cc nncn peano2cn sqrth 3brtr4d cc0 1nn0 rpge0 lt2sq
      nn0ge0i syl22anc mpbird ltadd1 syl3anc mpbid le2sq leadd2 ltletrd eqbrtrd
      pell14qrgap ) BCUAUBDZABUCEDZFAGHZUDZIBFJKZUEEZBUEEZJKZAILDWIUFMWIWKLDZWL
      LDZWMLDWIWKNDZWNWIWJNDZWPWIBNDZFNDZWQWIBCDZWRWFWGWTWHBCUAUGUHZBULOZWSWIUI
      MBFUJUKWJUMOZWKUNOZWIWLNDZWOWIWRXEXBBUMOZWLUNOZWKWLUOUKZWFWGALDWHABUPUQWI
      IFFJKZWMGIXIPWIURMWIXIWKFJKZWMXILDWIFFQQUSMWIWNXJLDXDWKUTOXHWIFWKGHZXIXJG
      HZWIXKFIRKZWKIRKZGHZWIFWJXMXNGWIFBWJFLDZWIQMZWIWTBLDZXABVBOZWIXRWJLDXSBUT
      OWIWTFBSHXABVAOZWIXRBWJGHXSBVCOVDXMFPWIVEMZWIWJVFDZXNWJPWIBVFDZYBWIWTYCXA
      BVGOZBVHOWJVIOVJWIXPVKFSHZWNVKWKSHZXKXOTXQYEWIFVLVOMZXDWIWPYFXCWKVMOFWKVN
      VPVQWIXPWNXPXKXLTXQXDXQFWKFVRVSVTWIFWLSHZXJWMSHZWIYHXMWLIRKZSHZWIFBXMYJSX
      TYAWIYCYJBPYDBVIOVJWIXPYEWOVKWLSHZYHYKTXQYGXGWIXEYLXFWLVMOFWLWAVPVQWIXPWO
      WNYHYITXQXGXDFWLWKWBVSVTWCWDABWEWC $.
      $( [18-Sep-2014] $)

    $( Condition for a calculated real to be a Pell solution. $)
    pellqrexplicit $p |- ( ( ( D e. ( NN \ []NN ) /\ A e. NN0 /\ B e. NN0 ) /\
        ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 ) -> ( A + ( ( sqr ` D ) x. B )
        ) e. ( Pell1QR ` D ) ) $=
      ( va vb cn wcel cn0 c2 cexp co cmul cmin c1 wceq wa caddc cr oveq1 oveq2d
      csquarenn cdif w3a csqr cfv cpell1qr cv wrex wb elpell1qr 3ad2ant1 adantr
      nn0re 3ad2ant2 crp eldifi nnrp rpsqrcl rpre 3syl 3ad2ant3 remulcl syl2anc
      syl readdcl simpl2 simpl3 eqidd simpr eqeq2d oveq1d eqeq1d oveq2 rcla42ev
      anbi12d syl112anc mpbir2and ) CFUAUBGZAHGZBHGZUCZAIJKZCBIJKZLKZMKZNOZPZAC
      UDUEZBLKZQKZCUFUEGZWJRGZWJDUGZWHEUGZLKZQKZOZWMIJKZCWNIJKZLKZMKZNOZPZEHUHD
      HUHZWAWKWLXDPUIZWFVRVSXEVTDEWJCUJUKULWAWLWFWAARGZWIRGZWLVSVRXFVTAUMUNWAWH
      RGZBRGZXGWACUOGZWHUOGXHWACFGZXJVRVSXKVTCFUAUPUKCUQVDCURWHUSUTVTVRXIVSBUMV
      AWHBVBVCAWIVEVCULWGVSVTWJWJOZWFXDVRVSVTWFVFVRVSVTWFVGWGWJVHWAWFVIXCXLWFPW
      JAWOQKZOZWBWTMKZNOZPDEABHHWMAOZWQXNXBXPXQWPXMWJWMAWOQSVJXQXAXONXQWRWBWTMW
      MAIJSVKVLVOWNBOZXNXLXPWFXRXMWJWJXRWOWIAQWNBWHLVMTVJXRXOWENXRWTWDWBMXRWSWC
      CLWNBIJSTTVLVOVNVPVQ $.
      $( [19-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Pell equations 3: characterizing fundamental solution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z A $.  $d x y z B $.
    $( Any lower bound of a nonempty set of real numbers is less than or equal
       to its infimum, one-direction version. $)
    infmrgelbi $p |- ( ( ( A C_ RR /\ A =/= (/) /\ B e. RR ) /\
                      A. x e. A B <_ x ) -> B <_ sup ( A , RR , `' < ) ) $=
      ( vz cr wss c0 wne wcel w3a cv cle wbr wral wa clt ccnv csup simpr wrex
      wb simpl1 simpl2 wceq ralbidv rcla4ev 3ad2antl3 simpl3 infmrgelb syl31anc
      breq1 mpbird ) BEFZBGHZCEIZJZCAKZLMZABNZOZCBEPQRLMZUSUPUSSUTUMUNDKZUQLMZA
      BNZDETZUOVAUSUAUMUNUOUSUBUMUNUOUSUCUOUMUSVEUNVDUSDCEVBCUDVCURABVBCUQLUKUE
      UFUGUMUNUOUSUHDAABCUIUJUL $.
      $( [1-Sep-2013] $)
  $}

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $( the only place we directly use D's non-squareness $)
    ${
      $d D x $.
      $( There is a nontrivial solution of a Pell equation in the first
         quadrant. $)
      pellqrex $p |- ( D e. ( NN \ []NN ) -> E. x e. ( Pell1QR ` D ) 1 < x ) $=
        ( vc vd va cn csquarenn wcel cv c2 cexp co c1 wceq wbr wa 1re a1i cle
        cr cdif cmul cmin wrex clt cpell1qr cfv csqr cq wn eldifi eldifn anim1i
        df-squarenn eleq2i fveq2 eleq1d elrab bitri sylibr mtand pellex syl2anc
        crab caddc cn0 simpll nnnn0 adantr ad2antlr adantl simpr pellqrexplicit
        syl31anc readdcli nnre ad2antrl crp nnrp syl rpsqrcl rpre 3syl ad2antll
        remulcl readdcl ltp1i nnge1 ax-1cn mulid2i sq1 cc nncn sqrth 3brtr4d wb
        cc0 1nn0 nn0ge0i rpge0 syl22anc mpbird wi jca lemul12a mp2and syl5eqbrr
        le2sq le2add ltletrd breq2 rcla4ev ex rexlimdvva mpd ) BFGUAHZCIZJKLBDI
        ZJKLUBLUCLMNZDFUDCFUDZMAIZUEOZABUFUGZUDZXPBFHZBUHUGZUIHZUJXTBFGUKZXPYGB
        GHZBFGULXPYGPYEYGPZYIXPYEYGYHUMYIBEIZUHUGZUIHZEFVDZHYJGYNBEUNUOYMYGEBFY
        KBNYLYFUIYKBUHUPUQURUSUTVACDBVBVCXPXSYDCDFFXPXQFHZXRFHZPZPZXSYDYRXSPZXQ
        YFXRUBLZVELZYCHZMUUAUEOZYDYSXPXQVFHZXRVFHZXSUUBXPYQXSVGYQUUDXPXSYOUUDYP
        XQVHVIVJYQUUEXPXSYPUUEYOXRVHVKVJYRXSVLXQXRBVMVNYRUUCXSYRMMMVELZUUAMTHZY
        RQRZUUFTHYRMMQQVORYRXQTHZYTTHZUUATHYOUUIXPYPXQVPVQZYRYFTHZXRTHZUUJYRBVR
        HZYFVRHZUULYRYEUUNXPYEYQYHVIZBVSZVTBWAZYFWBZWCZYPUUMXPYOXRVPWDZYFXRWEVC
        ZXQYTWFVCMUUFUEOYRMQWGRYRMXQSOZMYTSOZUUFUUASOZYOUVCXPYPXQWHVQYRMMMUBLZY
        TSMWIWJYRMYFSOZMXRSOZUVFYTSOZYRYEUVGUUPYEUVGMJKLZYFJKLZSOZYEMBUVJUVKSBW
        HUVJMNYEWKRYEBWLHUVKBNBWMBWNVTWOYEUUGWQMSOZUULWQYFSOZUVGUVLWPUUGYEQRUVM
        YEMWRWSZRYEUUNUUOUULUUQUURUUSWCYEUUNUUOUVNUUQUURYFWTWCMYFXHXAXBVTYPUVHX
        PYOXRWHWDYRUUGUVMPZUULUVPUUMUVGUVHPUVIXCYRUUGUVMUUHUVMYRUVORXDZUUTUVQUV
        AMYFMXRXEXAXFXGYRUUGUUGUUIUUJUVCUVDPUVEXCUUHUUHUUKUVBMMXQYTXIXAXFXJVIYB
        UUCAUUAYCYAUUAMUEXKXLVCXMXNXO $.
        $( [18-Sep-2014] $)
    $}

    ${
      $d D x $.
      $( Value of the fundamental solution of a Pell equation. $)
      pellfundval $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) = sup ( { x e.
          ( Pell14QR ` D ) | 1 < x } , RR , `' < ) ) $=
        ( va c1 cv clt wbr cpell14qr crab cr ccnv csup csquarenn cdif cpellfund
        cfv cn wceq fveq2 wor rabeq syl df-pellfund ltso cnvso mpbi supex fvmpt
        supeq1d ) CBDAEFGZACEZHPZIZJFKZLUJABHPZIZJUNLQMNOUKBRZJUMUPUNUQULUORUMU
        PRUKBHSUJAULUOUAUBUICAUCJUPUNJFTJUNTUDJFUEUFUGUH $.
        $( [18-Sep-2014] $)
    $}

    $( The fundamental solution of a Pell equation exists as a real number. $)
    pellfundre $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR ) $=
      ( va vb vc cn wcel cfv c1 cv clt wbr wss cle wral wrex pell14qrre sylancr
      cr 1re wa csquarenn cdif cpellfund cpell14qr crab ccnv pellfundval c0 wne
      csup ssrab2 ssrdv syl5ss cpell1qr pell1qrss14 pellqrex ssrexv sylc sylibr
      ex rabn0 breq2 elrab wi ltle expimpd syl5bi ralrimiv wceq ralbidv rcla4ev
      breq1 infmrcl syl3anc eqeltrd ) AEUAUBFZAUCGHBIZJKZBAUDGZUEZRJUFUJZRBAUGV
      PVTRLVTUHUIZCIZDIZMKZDVTNZCROZWARFVPVTVSRVRBVSUKVPBVSRVPVQVSFVQRFVQAPUTUL
      UMVPVRBVSOZWBVPAUNGZVSLVRBWIOWHAUOBAUPVRBWIVSUQURVRBVSVAUSVPHRFZHWDMKZDVT
      NZWGSVPWKDVTWDVTFWDVSFZHWDJKZTVPWKVRWNBWDVSVQWDHJVBVCVPWMWNWKVPWMTWJWDRFW
      NWKVDSWDAPHWDVEQVFVGVHWFWLCHRWCHVIWEWKDVTWCHWDMVLVJVKQCDVTVMVNVO $.
      $( [18-Sep-2014] $)

    $( Lower bound on the fundamental solution of a Pell equation. $)
    pellfundge $p |- ( D e. ( NN \ []NN ) -> ( ( sqr ` ( D + 1 ) ) + ( sqr ` D
        ) ) <_ ( PellFund ` D ) ) $=
      ( va vb cn csquarenn wcel c1 caddc co csqr cfv cv clt wbr cr cle wss wrex
      crp 3syl cdif cpell14qr crab ccnv csup cpellfund c0 wne ssrab2 pell14qrre
      wral ssrdv syl5ss cpell1qr pell1qrss14 pellqrex ssrexv sylc sylibr eldifi
      ex rabn0 peano2nn nnrp rpsqrcl rpre syl readdcl syl2anc breq2 pell14qrgap
      wa elrab 3expib syl5bi ralrimiv infmrgelbi syl31anc pellfundval breqtrrd
      ) ADEUAFZAGHIZJKZAJKZHIZGBLZMNZBAUBKZUCZOMUDUEZAUFKPWAWIOQWIUGUHZWEOFZWEC
      LZPNZCWIUKWEWJPNWAWIWHOWGBWHUIWABWHOWAWFWHFWFOFWFAUJVAULUMWAWGBWHRZWKWAAU
      NKZWHQWGBWPRWOAUOBAUPWGBWPWHUQURWGBWHVBUSWAWCOFZWDOFZWLWAWBSFZWCSFWQWAADF
      ZWBDFWSADEUTZAVCWBVDTWBVEWCVFTWAASFZWDSFWRWAWTXBXAAVDVGAVEWDVFTWCWDVHVIWA
      WNCWIWMWIFWMWHFZGWMMNZVLWAWNWGXDBWMWHWFWMGMVJVMWAXCXDWNWMAVKVNVOVPCWIWEVQ
      VRBAVSVT $.
      $( [19-Sep-2014] $)

    $( Weak lower bound on the Pell fundamental solution. $)
    pellfundgt1 $p |- ( D e. ( NN \ []NN ) -> 1 < ( PellFund ` D ) ) $=
      ( cn csquarenn wcel c1 caddc co csqr cfv cr a1i crp syl nnrp 3syl wbr cle
      sqr1 cc0 wa cdif cpellfund 1re eldifi peano2nn rpsqrcl readdcl pellfundre
      rpre syl2anc wceq eqeltrd clt 1lt2 oveq12i 1p1e2apr1 eqtri breqtrri nnge1
      c2 wb nnre peano2re 1nn0 nn0ge0i nnnn0 nn0ge0 sqrle syl22anc mpbid le2add
      cn0 3impia syl222anc ltletrd pellfundge ) ABCUADZEAEFGZHIZAHIZFGZAUBIEJDZ
      VQUCKZVQVSJDZVTJDZWAJDVQVRLDZVSLDWDVQVRBDZWFVQABDZWGABCUDZAUEMZVRNMVRUFVS
      UIOZVQALDZVTLDWEVQWHWLWIANMAUFVTUIOZVSVTUGUJZAUHVQEEHIZWOFGZWAWCVQWOJDZWQ
      WPJDVQWOEJWOEUKVQRKWCULZWRWOWOUGUJWNEWPUMPVQEUTWPUMUNWPEEFGUTWOEWOEFRRUOU
      PUQURKVQWQWQWDWEWOVSQPZWOVTQPZWPWAQPZWRWRWKWMVQEVRQPZWSVQWGXBWJVRUSMVQWBV
      RJDZSEQPZSVRQPZXBWSVAWCVQAJDZXCVQWHXFWIAVBMZAVCMXDVQEVDVEKZVQWGVRVLDXEWJV
      RVFVRVGOEVRVHVIVJVQEAQPZWTVQWHXIWIAUSMVQWBXFXDSAQPZXIWTVAWCXGXHVQWHAVLDXJ
      WIAVFAVGOEAVHVIVJWQWQTWDWETWSWTTXAWOWOVSVTVKVMVNVOAVPVO $.
      $( [19-Sep-2014] $)

    $( A nontrivial first quadrant solution is at least as large as the
       fundamental solution. $)
    pellfundlb $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A )
        -> ( PellFund ` D ) <_ A ) $=
      ( va vb vc vd wcel cfv c1 clt wbr cv cr cle wceq 3ad2ant1 wral pell14qrre
      1re wa csquarenn cdif cpell14qr cpellfund crab ccnv csup pellfundval wrex
      cn w3a wss ssrab2 ex ssrdv syl5ss breq2 elrab ltle sylancr expimpd syl5bi
      wi ralrimiv breq1 ralbidv rcla4ev simp2 sylanbrc infmrlb syl3anc eqbrtrd
      simp3 ) BUJUAUBGZABUCHZGZIAJKZUKZBUDHZICLZJKZCVOUEZMJUFUGZANVNVPVSWCOVQCB
      UHPVRWBMULZDLZELZNKZEWBQZDMUIZAWBGZWCANKVNVPWDVQVNWBVOMWACVOUMVNFVOMVNFLZ
      VOGWKMGWKBRUNUOUPPVRIMGZIWFNKZEWBQZWISVNVPWNVQVNWMEWBWFWBGWFVOGZIWFJKZTVN
      WMWAWPCWFVOVTWFIJUQURVNWOWPWMVNWOTWLWFMGWPWMVCSWFBRIWFUSUTVAVBVDPWHWNDIMW
      EIOWGWMEWBWEIWFNVEVFVGUTVRVPVQWJVNVPVQVHVNVPVQVMWAVQCAVOVTAIJUQURVIDEAWBV
      JVKVL $.
      $( [19-Sep-2014] $)

    ${
      $d x D $.  $d x A $.
      $( If a real is larger than the fundamental solution, there is a
         nontrivial solution less than it. $)
      pellfundglb $p |- ( ( D e. ( NN \ []NN ) /\ A e. RR /\ ( PellFund ` D ) <
          A ) -> E. x e. ( Pell1QR ` D ) ( ( PellFund ` D ) <_ x /\ x < A ) )
          $=
        ( va wcel cr cfv clt wbr cle wn c1 wrex wa 3ad2ant1 wb syl2anc wss wi
        ex cn csquarenn cdif cpellfund w3a cv cpell14qr crab cpell1qr wral ccnv
        csup wceq pellfundval simp3 eqbrtrrd pellfundre eqeltrrd simp2 ltnle c0
        mpbid ssrab2 pell14qrre ssrdv syl5ss pell1qrss14 pellqrex ssrexv sylibr
        wne sylc rabn0 infmrgelbi syl3anc mtod rexnal breq2 elrab simprl simprr
        1re a1i simpl1 ltle mpd jca elpell1qr2 syl mpbird sylan2b adantrr simpr
        sseldi syl5bi imp pellfundlb adantr sseldd simpl2 reximdv2 ) CUAUBUCEZB
        FEZCUDGZBHIZUEZBAUFZJIZKZALDUFZHIZDCUGGZUHZMZXDXGJIZXGBHIZNZACUIGZMXFXH
        AXMUJZKXNXFXSBXMFHUKULZJIZXFXTBHIZYAKZXFXDXTBHXBXCXDXTUMXEDCUNOZXBXCXEU
        OUPXFXTFEXCYBYCPXFXDXTFYDXBXCXDFEXECUQOURXBXCXEUSZXTBUTQVBXFXMFRZXMVAVK
        ZXCXSYASXFXMXLFXKDXLVCZXBXCXLFRZXEXBDXLFXBXJXLEXJFEXJCVDTVEOZVFXFXKDXLM
        ZYGXFXRXLRZXKDXRMZYKXBXCYLXECVGOXBXCYMXEDCVHOXKDXRXLVIVLXKDXLVMVJYEYFYG
        XCUEXSYAAXMBVNTVOVPXHAXMVQVJXFXIXQAXMXRXFXGXMEZXINZXGXREZXQNXFYONZYPXQX
        FYNYPXIYNXFXGXLEZLXGHIZNZYPXKYSDXGXLXJXGLHVRVSZXFYTNZYPYRLXGJIZNZUUBYRU
        UCXFYRYSVTZUUBYSUUCXFYRYSWAUUBLFEZXGFEZYSUUCSUUFUUBWBWCUUBXBYRUUGXBXCXE
        YTWDZUUEXGCVDQLXGWEQWFWGUUBXBYPUUDPUUHXGCWHWIWJWKWLYQXOXPYQXBYRYSXOXBXC
        XEYOWDYQXMXLXGYHXFYNXIVTWNZXFYNYSXIXFYNYSYNYTXFYSUUAYTYSSXFYRYSWMWCWOWP
        WLXGCWQVOYQXPXIXFYNXIWAYQUUGXCXPXIPYQXLFXGXFYIYOYJWRUUIWSXBXCXEYOWTXGBU
        TQWJWGWGTXAWF $.
        $( [18-Sep-2014] $)
    $}

    $( use the infimum to find an element ge Fund and lt 2*Fund.  if = Fund we're done, otherwise use the infimum again to find another element which must be ge Fund and lt the first element; their ratio is a group element in (1,2), contradicting pell1qrgapw $)
    $( The fundamental solution as an infimum is itself a solution, showing
       that the solution set is discrete. $)
    pellfundex $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. ( Pell1QR ` D
        ) ) $=
      ( va vb wcel cfv cle wbr c2 co clt wa cr 2re cc0 c1 a1i syl2anc wb adantr
      ad3antrrr cn csquarenn cdif cpellfund cv cmul cpell1qr pellfundre remulcl
      wrex sylancr caddc crp 0reALT 1re lt01 pellfundgt1 lttrd sylanbrc ltaddrp
      elrp cc wceq recnd 2times breqtrrd pellfundglb mpd3an23 wo wi pell1qrss14
      syl cpell14qr sselda pell14qrre syldan leloe simpll simprl syl3anc simplr
      simpl simpr simprr wss sseldd ad2antrr lemul2 syl112anc mpbid ltletrd w3a
      2pos simp1 3ad2ant1 simp2l simp2r pell14qrdivcl mulid2 simp3l pell14qrgt0
      cdiv eqbrtrd ltmuldiv simp3r ltdivmul2 mpbird wn pell14qrgapw ltnsym sylc
      mpd pm2.24 syl22anc syl122anc ex rexlimdva exp32 simp1r eqeltrd 3exp jaod
      simp2 sylbid imp3a ) AUAUBUCDZAUDEZBUEZFGZYHHYGUFIZJGZKZBAUGEZUJZYGYMDZYF
      YJLDZYGYJJGYNYFHLDZYGLDZYPMAUHZHYGUIUKZYFYGYGYGULIZYJJYFYRYGUMDZYGUUAJGYS
      YFYRNYGJGUUBYSYFNOYGNLDYFUNPOLDZYFUOPYSNOJGYFUPPAUQURYGVAUSYGYGUTQYFYGVBD
      YJUUAVCYFYGYSVDYGVEVLVFBYJAVGVHYFYLYOBYMYFYHYMDZKZYIYKYOUUEYIYGYHJGZYGYHV
      CZVIZYKYOVJZUUEYRYHLDZYIUUHRYFYRUUDYSSZYFUUDYHAVMEZDZUUJYFYMUULYHAVKZVNYH
      AVOZVPZYGYHVQQUUEUUFUUIUUGUUEUUFYKYOUUEUUFYKKZKZYGCUEZFGZUUSYHJGZKZCYMUJZ
      YOUURYFUUJUUFUVCYFUUDUUQVRUUEUUJUUQUUPSUUEUUFYKVSCYHAVGVTUURUVBYOCYMUURUU
      SYMDZKZUVBYOUVEUVBKZYFUUDUVDUVAYHHUUSUFIZJGZYOUUEYFUUQUVDUVBYFUUDWBTZUUEU
      UDUUQUVDUVBYFUUDWCTUURUVDUVBWAZUVEUUTUVAWDUVFYHYJUVGUUEUUJUUQUVDUVBUUPTUU
      EYPUUQUVDUVBYFYPUUDYTSTUVFYQUUSLDZUVGLDMUVFYFUUSUULDZUVKUVIUVFYMUULUUSUUE
      YMUULWEZUUQUVDUVBYFUVMUUDUUNSTUVJWFUUSAVOZQZHUUSUIUKUURYKUVDUVBUUEUUFYKWD
      WGUVFUUTYJUVGFGZUVEUUTUVAVSUVFYRUVKYQNHJGZUUTUVPRUUEYRUUQUVDUVBUUKTUVOYQU
      VFMPUVQUVFWMPYGUUSHWHWIWJWKYFUUDUVDKZUVAUVHKZWLZYFYHUUSXBIZUULDZOUWAJGZUW
      AHJGZYOYFUVRUVSWNZUVTYFUUMUVLUWBUWEUVTYMUULYHYFUVRUVMUVSUUNWOZYFUUDUVDUVS
      WPWFZUVTYMUULUUSUWFYFUUDUVDUVSWQWFZYHUUSAWRVTUVTOUUSUFIZYHJGZUWCUVTUWIUUS
      YHJUVTUUSVBDUWIUUSVCUVTUUSUVTYFUVLUVKUWEUWHUVNQZVDUUSWSVLYFUVRUVAUVHWTXCU
      VTUUCUUJUVKNUUSJGZUWJUWCRUUCUVTUOPUVTYFUUMUUJUWEUWGUUOQZUWKUVTYFUVLUWLUWE
      UWHUUSAXAQZOYHUUSXDWIWJUVTUWDUVHYFUVRUVAUVHXEUVTUUJYQUVKUWLUWDUVHRUWMYQUV
      TMPUWKUWNYHHUUSXFWIXGYFUWBKZUWCUWDKZKZUWDUWDXHZYOUWOUWCUWDWDUWQHUWAJGZUWR
      UWQYFUWBUWCUWSYFUWBUWPVRYFUWBUWPWAUWOUWCUWDVSUWAAXIVTUWQYQUWALDZUWSUWRVJM
      UWOUWTUWPUWAAVOSHUWAXJUKXLUWDYOXMXKXNXOXPXQXLXRUUEUUGYKYOUUEUUGYKWLYGYHYM
      UUEUUGYKYCYFUUDUUGYKXSXTYAYBYDYEXQXL $.
      $( [18-Sep-2014] $)

    $( There are no solutions between 1 and the fundamental solution. $)
    pellfund14gap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ ( 1
        <_ A /\ A < ( PellFund ` D ) ) ) -> A = 1 ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv c1 cle wbr cpellfund clt wa w3a wn
      wceq cr wb mpbid wo simp3r pell14qrre 3adant3 pellfundre 3ad2ant1 syl2anc
      ltnle simpl1 simpl2 simpr pellfundlb syl3anc mtand simp3l 1re leloe orel1
      sylancr sylc eqcomd ) BCDEFZABGHFZIAJKZABLHZMKZNZOZIAVHIAMKZPVIIAQZUAZVJV
      HVIVEAJKZVHVFVLPZVBVCVDVFUBVHARFZVERFZVFVMSVBVCVNVGABUCUDZVBVCVOVGBUEUFAV
      EUHUGTVHVINVBVCVIVLVBVCVGVIUIVBVCVGVIUJVHVIUKABULUMUNVHVDVKVBVCVDVFUOVHIR
      FVNVDVKSUPVPIAUQUSTVIVJURUTVA $.
      $( [18-Sep-2014] $)

    $( The fundamental Pell solution is a positive real. $)
    pellfundrp $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR+ ) $=
      ( cn csquarenn cdif wcel cpellfund cfv cc0 clt wbr crp pellfundre 0re a1i
      cr c1 1re lt01 pellfundgt1 lttrd elrp sylanbrc ) ABCDEZAFGZOEHUDIJUDKEALZ
      UCHPUDHOEUCMNPOEUCQNUEHPIJUCRNASTUDUAUB $.
      $( [19-Sep-2014] $)

    $( The fundamental Pell solution is never 1. $)
    pellfundne1 $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) =/= 1 ) $=
      ( cn csquarenn cdif wcel c1 cpellfund cfv clt wbr wne 1re a1i pellfundgt1
      cr pellfundre ltne syl3anc ) ABCDEZFOEZAGHZOEFUAIJUAFKTSLMAPANFUAQR $.
      $( [19-Sep-2014] $)

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Logarithm laws generalized to an arbitrary base
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $( Logarithm of a non-1 number is not zero and thus suitible as a divisor.
       We will be representing the general-base logarithm as a quotient of
       natural logarithms. $)
    logne0 $p |- ( ( A e. RR+ /\ A =/= 1 ) -> ( log ` A ) =/= 0 ) $=
      ( crp wcel c1 wne wa clog cfv cc0 ce simpr wceq ef0 neeqtrrd necomd cr wb
      a1i 0re relogeftb syldan necon3bid mpbird ) ABCZADEZFZAGHZIEIJHZAEUFAUHUF
      ADUHUDUEKUHDLUFMRNOUFUGIUHAUDUEIPCZUGILUHALQUIUFSRAITUAUBUC $.
      $( [19-Sep-2014] $)

    $( General logarithm is a real number. $)
    reglogcl $p |- ( ( A e. RR+ /\ B e. RR+ /\ B =/= 1 ) -> ( ( log ` A ) / (
        log ` B ) ) e. RR ) $=
      ( crp wcel c1 wne w3a clog cfv cr cc0 co relogcl 3ad2ant1 3ad2ant2 logne0
      cdiv 3adant1 redivcl syl3anc ) ACDZBCDZBEFZGAHIZJDZBHIZJDZUFKFZUDUFQLJDUA
      UBUEUCAMNUBUAUGUCBMOUBUCUHUABPRUDUFST $.
      $( [19-Sep-2014] $)

    $( General logarithm preserves "less than". $)
    reglogltb $p |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) ->
        ( A < B <-> ( ( log ` A ) / ( log ` C ) ) < ( ( log ` B ) / ( log ` C )
        ) ) ) $=
      ( crp wcel wa c1 clt wbr clog cfv cdiv co wb logltb adantr cr cc0 relogcl
      ad2antrr ad2antlr ad2antrl log1 mpan biimpa syl5eqbrr adantl ltdiv1 bitrd
      1rp syl112anc ) ADEZBDEZFZCDEZGCHIZFZFZABHIZAJKZBJKZHIZUTCJKZLMVAVCLMHIZU
      NUSVBNUQABOPURUTQEZVAQEZVCQEZRVCHIZVBVDNULVEUMUQASTUMVFULUQBSUAUOVGUNUPCS
      UBUQVHUNUQRGJKZVCHUCUOUPVIVCHIZGDEUOUPVJNUJGCOUDUEUFUGUTVAVCUHUKUI $.
      $( [19-Sep-2014] $)

    $( Natural logarithm preserves ` <_ ` . $)
    logleb $p |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A <_ B <-> ( log ` A ) <_ (
        log ` B ) ) ) $=
      ( crp wcel wa clt wbr wn clog cfv cle wb logltb ancoms notbid rpre syl2an
      cr lenlt relogcl 3bitr4d ) ACDZBCDZEZBAFGZHZBIJZAIJZFGZHZABKGZUHUGKGZUDUE
      UIUCUBUEUILBAMNOUBARDBRDUKUFLUCAPBPABSQUBUHRDUGRDULUJLUCATBTUHUGSQUA $.
      $( [19-Sep-2014] $)

    $( General logarithm preserves ` <_ ` . $)
    reglogleb $p |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) ->
        ( A <_ B <-> ( ( log ` A ) / ( log ` C ) ) <_ ( ( log ` B ) / ( log ` C
        ) ) ) ) $=
      ( crp wcel wa c1 clt wbr cle clog cfv cdiv co wb logleb adantr cr relogcl
      cc0 ad2antrr ad2antlr ad2antrl log1 logltb biimpa syl5eqbrr adantl lediv1
      1rp mpan syl112anc bitrd ) ADEZBDEZFZCDEZGCHIZFZFZABJIZAKLZBKLZJIZVBCKLZM
      NVCVEMNJIZUPVAVDOUSABPQUTVBREZVCREZVEREZTVEHIZVDVFOUNVGUOUSASUAUOVHUNUSBS
      UBUQVIUPURCSUCUSVJUPUSTGKLZVEHUDUQURVKVEHIZGDEUQURVLOUJGCUEUKUFUGUHVBVCVE
      UIULUM $.
      $( [19-Oct-2014] $)

    $( Multiplication law for general log. $)
    reglogmul $p |- ( ( A e. RR+ /\ B e. RR+ /\ ( C e. RR+ /\ C =/= 1 ) ) -> (
        ( log ` ( A x. B ) ) / ( log ` C ) ) = ( ( ( log ` A ) / ( log ` C ) )
        + ( ( log ` B ) / ( log ` C ) ) ) ) $=
      ( crp wcel c1 wne wa w3a cmul co clog cdiv caddc wceq cc relogcl 3ad2ant3
      cfv recnd relogmul 3adant3 oveq1d 3ad2ant1 adantr logne0 divdir syl112anc
      cc0 3ad2ant2 eqtrd ) ADEZBDEZCDEZCFGZHZIZABJKLSZCLSZMKALSZBLSZNKZUSMKZUTU
      SMKVAUSMKNKZUQURVBUSMULUMURVBOUPABUAUBUCUQUTPEZVAPEZUSPEZUSUIGZVCVDOULUMV
      EUPULUTAQTUDUMULVFUPUMVABQTUJUPULVGUMUNVGUOUNUSCQTUERUPULVHUMCUFRUTVAUSUG
      UHUK $.
      $( [19-Sep-2014] $)

    $( Power law for general log. $)
    reglogexp $p |- ( ( A e. RR+ /\ N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( (
        log ` ( A ^ N ) ) / ( log ` C ) ) = ( N x. ( ( log ` A ) / ( log ` C )
        ) ) ) $=
      ( crp wcel cz c1 wne wa w3a co clog cdiv cmul wceq relogcl recnd 3ad2ant3
      cfv cc cexp relogexp 3adant3 oveq1d cc0 zcn 3ad2ant2 adantr logne0 divass
      3ad2ant1 syl112anc eqtrd ) ADEZCFEZBDEZBGHZIZJZACUAKLSZBLSZMKCALSZNKZVAMK
      ZCVBVAMKNKZUSUTVCVAMUNUOUTVCOURACUBUCUDUSCTEZVBTEZVATEZVAUEHZVDVEOUOUNVFU
      RCUFUGUNUOVGURUNVBAPQUKURUNVHUOUPVHUQUPVABPQUHRURUNVIUOBUIRCVBVAUJULUM $.
      $( [19-Sep-2014] $)

    $( General log of the base is 1. $)
    reglogbas $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` C ) / ( log ` C ) )
        = 1 ) $=
      ( crp wcel c1 wne wa clog cfv cc cdiv co wceq relogcl recnd adantr logne0
      cc0 divid syl2anc ) ABCZADEZFAGHZICZUBQEUBUBJKDLTUCUATUBAMNOAPUBRS $.
      $( [19-Sep-2014] $)

    $( General log of 1 is 0. $)
    reglog1 $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` 1 ) / ( log ` C ) ) =
        0 ) $=
      ( crp wcel c1 wne wa clog cfv cdiv co cc0 log1 oveq1i wceq relogcl adantr
      cc recnd logne0 div0 syl2anc syl5eq ) ABCZADEZFZDGHZAGHZIJKUGIJZKUFKUGILM
      UEUGQCZUGKEUHKNUCUIUDUCUGAORPASUGTUAUB $.
      $( [19-Sep-2014] $)

    $( General log of a power of the base is the exponent. $)
    reglogexpbas $p |- ( ( N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( ( log ` (
        C ^ N ) ) / ( log ` C ) ) = N ) $=
      ( cz wcel crp c1 wne wa cexp co clog cfv cdiv cmul simprl simpl reglogexp
      wceq simpr syl3anc reglogbas adantl oveq2d zcn adantr mulid1 syl 3eqtrd
      cc ) BCDZAEDZAFGZHZHZABIJKLAKLZMJZBUOUOMJZNJZBFNJZBUNUKUJUMUPURRUJUKULOUJ
      UMPUJUMSAABQTUNUQFBNUMUQFRUJAUAUBUCUNBUIDZUSBRUJUTUMBUDUEBUFUGUH $.
      $( [19-Sep-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Pell equations 4: the positive solution group is infinite cyclic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.


    ${
      $d x D $.  $d x A $.
      $( Every positive Pell solution is a power of the fundamental
         solution. $)
      pellfund14 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> E.
          x e. ZZ A = ( ( PellFund ` D ) ^ x ) ) $=
        ( wcel cfv clog cdiv co cz cexp wceq crp c1 syl cle wbr clt cc0 syl2anc
        cc cn csquarenn cdif cpell14qr cpellfund cfl wrex pell14qrrp pellfundrp
        wa cv cr adantr pellfundne1 reglogcl syl3anc flcl cneg cmul caddc simpl
        wne cpell1qr pell1qrss14 pellfundex sseldd znegcl pell14qrexpcl mpd3an3
        pell14qrmulcl cmo 1rp a1i modge0 cmin recnd zcn negsub modfrac breqtrrd
        eqtr4d reglog1 rpexpcl reglogmul syl112anc reglogexpbas syl12anc oveq2d
        eqtrd 3brtr4d wb rpmulcl pellfundgt1 reglogleb syl22anc modlt reglogbas
        mpbird eqbrtrd reglogltb pellfund14gap negid rpcn eqtr2d expaddz 3eqtrd
        exp0 rpne0 pell14qrre mulcan2 mpbid oveq2 eqeq2d rcla4ev ) CUAUBUCDZBCU
        DEZDZUJZBFECUEEZFEZGHZUFEZIDZBXSYBJHZKZBXSAUKZJHZKZAIUGXRYAULDZYCXRBLDZ
        XSLDZXSMVBZYIBCUHZXOYKXQCUIUMZXOYLXQCUNUMZBXSUOUPZYAUQNZXRBXSYBURZJHZUS
        HZYDYSUSHZKZYEXRYTMXSYBYRUTHZJHZUUAXRXOYTXPDZMYTOPZYTXSQPZYTMKXOXQVAZXO
        XQYSXPDZUUEXRXOXSXPDZYRIDZUUIUUHXOUUJXQXOCVCEXPXSCVDCVEVFUMXRYCUUKYQYBV
        GNZXSYRCVHUPBYSCVJVIXRUUFMFEXTGHZYTFEXTGHZOPZXRRYAYRUTHZUUMUUNOXRRYAMVK
        HZUUPOXRYIMLDZRUUQOPYPUURXRVLVMZYAMVNSXRUUPYAYBVOHZUUQXRYATDYBTDZUUPUUT
        KXRYAYPVPXRYCUVAYQYBVQNZYAYBVRSXRYIUUQUUTKYPYAVSNWAZVTXRYKYLUUMRKYNYOXS
        WBSXRUUNYAYSFEXTGHZUTHZUUPXRYJYSLDZYKYLUUNUVEKYMXRYKUUKUVFYNUULXSYRWCSZ
        YNYOBYSXSWDWEXRUVDYRYAUTXRUUKYKYLUVDYRKUULYNYOXSYRWFWGWHWIZWJXRUURYTLDZ
        YKMXSQPZUUFUUOWKUUSXRYJUVFUVIYMUVGBYSWLSZYNXOUVJXQCWMUMZMYTXSWNWOWRXRUU
        GUUNXTXTGHZQPZXRUUPMUUNUVMQXRUUPUUQMQUVCXRYIUURUUQMQPYPUUSYAMWPSWSUVHXR
        YKYLUVMMKYNYOXSWQSWJXRUVIYKYKUVJUUGUVNWKUVKYNYNUVLYTXSXSWTWOWRYTCXAWEXR
        UUDXSRJHZMXRUUCRXSJXRUVAUUCRKUVBYBXBNWHXRXSTDZUVOMKXRYKUVPYNXSXCNZXSXGN
        XDXRUVPXSRVBZYCUUKUUDUUAKUVQXRYKUVRYNXSXHNYQUULXSYBYRXEWOXFXRBTDYDTDZYS
        TDZYSRVBZUUBYEWKXRBBCXIVPXRYDLDZUVSXRYKYCUWBYNYQXSYBWCSYDXCNXRUVFUVTUVG
        YSXCNXRUVFUWAUVGYSXHNBYDYSXJWEXKYHYEAYBIYFYBKYGYDBYFYBXSJXLXMXNS $.
        $( [19-Sep-2014] $)

      $( The positive Pell solutions are precisely the integer powers of the
         fundamental solution.  To get the general solution set (which we will
         not be using), throw in a copy of Z/2Z. $)
      pellfund14b $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> E.
          x e. ZZ A = ( ( PellFund ` D ) ^ x ) ) ) $=
        ( cn csquarenn cdif wcel cpell14qr cpellfund cv cexp co wceq pellfund14
        cfv cz wrex wa simpll cpell1qr pellfundex sseldd ad2antrr pell14qrexpcl
        pell1qrss14 simplr syl3anc wb eleq1 adantl mpbird rexlimdva imp impbida
        ex ) CDEFGZBCHOZGZBCIOZAJZKLZMZAPQZABCNUPVCURUPVBURAPUPUTPGZRZVBURVEVBR
        ZURVAUQGZVFUPUSUQGZVDVGUPVDVBSUPVHVDVBUPCTOUQUSCUECUAUBUCUPVDVBUFUSUTCU
        DUGVBURVGUHVEBVAUQUIUJUKUOULUMUN $.
        $( [19-Sep-2014] $)
    $}

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    X and Y sequences 1: Definition and recurrence laws
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c rmX rmY $.

  $( Extend class notation to include the Robertson-Matiyasevich X sequence. $)
  crmx $a class rmX $.
  $( Extend class notation to include the Robertson-Matiyasevich Y sequence. $)
  crmy $a class rmY $.

  ${
    $d a n b c $.
    $( Define the X sequence as the rational part of some solution of a special
       Pell equation.  See ~ frmx and ~ rmxyval for a more useful but
       non-eliminable definition. $)
    df-rmx $a |- rmX = ( a e. ( ZZ>= ` 2 ) , n e. ZZ |-> ( 1st ` ( `' ( b e. (
        NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( a ^ 2 ) - 1 ) ) x. ( 2nd
        ` b ) ) ) ) ` ( ( a + ( sqr ` ( ( a ^ 2 ) - 1 ) ) ) ^ n ) ) ) ) $.
    $( Define the X sequence as the irrational part of some solution of a
       special Pell equation.  See ~ frmy and ~ rmxyval for a more useful but
       non-eliminable definition. $)
    df-rmy $a |- rmY = ( a e. ( ZZ>= ` 2 ) , n e. ZZ |-> ( 2nd ` ( `' ( b e. (
        NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( a ^ 2 ) - 1 ) ) x. ( 2nd
        ` b ) ) ) ) ` ( ( a + ( sqr ` ( ( a ^ 2 ) - 1 ) ) ) ^ n ) ) ) ) $.
  $}

  ${
    $d a n b A $.  $d a n b N $.
    $( Value of the X sequence.  Not used after ~ rmxyval is proved. $)
    rmxfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) = ( 1st ` (
        `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqr caddc c1st cmul cmpt ccnv wceq
      cuz cn0 cxp c2nd eqidd oveq1 oveq1d fveq2d oveq2d mpteq12dv cnveqd adantr
      crmx wa id1 oveq12d oveqan12d fveq12d df-rmx fvex ovmpt2a ) DEABFUAGHDIZV
      BFJKZLMKZNGZOKZEIZJKZCUBHUCZCIZPGZVEVJUDGZQKZOKZRZSZGZPGAAFJKZLMKZNGZOKZB
      JKZCVIVKVTVLQKZOKZRZSZGZPGUMVBATZVGBTZUNZVQWGPWJVHWBVPWFWHVPWFTWIWHVOWEWH
      CVIVNVIWDWHVIUEWHVMWCVKOWHVEVTVLQWHVDVSNWHVCVRLMVBAFJUFUGUHZUGUIUJUKULWHW
      IVFWAVGBJWHVBAVEVTOWHUOWKUPWIUOUQURUHEDCUSWGPUTVA $.
      $( [21-Sep-2014] $)

    $( Value of the Y sequence.  Not used after ~ rmxyval is proved. $)
    rmyfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY N ) = ( 2nd ` (
        `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqr caddc c2nd cmul cmpt ccnv wceq
      cuz cn0 cxp c1st eqidd oveq1 oveq1d fveq2d oveq2d mpteq12dv cnveqd adantr
      crmy wa id1 oveq12d id oveqan12d fveq12d df-rmy fvex ovmpt2a ) DEABFUAGHD
      IZVCFJKZLMKZNGZOKZEIZJKZCUBHUCZCIZUDGZVFVKPGZQKZOKZRZSZGZPGAAFJKZLMKZNGZO
      KZBJKZCVJVLWAVMQKZOKZRZSZGZPGUMVCATZVHBTZUNZVRWHPWKVIWCVQWGWIVQWGTWJWIVPW
      FWICVJVOVJWEWIVJUEWIVNWDVLOWIVFWAVMQWIVEVTNWIVDVSLMVCAFJUFUGUHZUGUIUJUKUL
      WIWJVGWBVHBJWIVCAVFWAOWIUOWLUPWJUQURUSUHEDCUTWHPVAVB $.
      $( [21-Sep-2014] $)
  $}

  $( The discriminant used to define the X and Y sequences has an irrational
     square root. $)
  rmspecsqrnq $p |- ( A e. ( ZZ>= ` 2 ) -> ( sqr ` ( ( A ^ 2 ) - 1 ) ) e. ( CC
      \ QQ ) ) $=
    ( c2 wcel cexp co c1 cmin cc cq 3syl a1i syl2anc syl clt caddc cmul wceq cr
    wbr remulcl cuz cfv csqr wn cdif cz uzssz sseli zcn sqcl ax-1cn subcl sqrcl
    cn0 cn wa eluz2b2 biimpi simpld nnsqcl nnm1nn0 eluzelre recnd binom2sub 2re
    1re resqcli recni subsub syl3anc eqtr4d 2timesi eqcomi simprd cc0 wb ltmul2
    syl112anc mpbid eqbrtrd ltaddsub mulid1 oveq2d sq1 oveq12d breqtrrd resubcl
    2pos nnre ltsub2 ltm1 npcan oveq1d nonsq syl22anc eldif sylanbrc ) ABUAUBZC
    ZABDEZFGEZUCUBZHCZXBICUDZXBHIUECWSXAHCZXCWSWTHCZFHCZXEWSAUFCAHCZXFWRUFABUGU
    HAUIAUJJZXGWSUKKZWTFULLXAUMMWSXAUNCZAFGEZUNCZXLBDEZXANSXAXLFOEZBDEZNSXDWSAU
    OCZWTUOCZXKWSXQFANSZWSXQXSUPAUQURZUSZAUTZWTVAJWSXQXMYAAVAMWSXNWTBAFPEZPEZFB
    DEZGEZGEZXANWSXNWTYDGEYEOEZYGWSXHXGXNYHQWSABAVBZVCZXJAFVDLWSXFYDHCYEHCZYGYH
    QXIWSYDWSBRCZYCRCZYDRCZYLWSVEKZWSARCZFRCZYMYIYQWSVFKZAFTLBYCTLZVCYKWSYEFVFV
    GZVHKWTYDYEVIVJVKWSFYFNSZYGXANSZWSFBAPEZFGEZYFNWSFFOEZUUCNSZFUUDNSZWSUUEBFP
    EZUUCNUUEUUHQWSUUHUUEFUKVLVMKWSXSUUHUUCNSZWSXQXSXTVNWSYQYPYLVOBNSZXSUUIVPYR
    YIYOUUJWSWHKFABVQVRVSVTWSYQYQUUCRCZUUFUUGVPYRYRWSYLYPUUKYOYIBATLFFUUCWAVJVS
    WSYDUUCYEFGWSYCABPWSXHYCAQYJAWBMWCYEFQWSWDKWEWFWSYQYFRCZWTRCZUUAUUBVPYRWSYN
    YERCZUULYSUUNWSYTKYDYEWGLWSXQXRUUMYAYBWTWIJZFYFWTWJVJVSVTWSXAWTXPNWSUUMXAWT
    NSUUOWTWKMWSXOABDWSXHXGXOAQYJXJAFWLLWMWFXAXLWNWOXBHIWPWQ $.
    $( [21-Sep-2014] $)

  ${
    $d a A $.
    $( The discriminant used to define the X and Y sequences is a nonsquare
       positive integer and thus a valid Pell equation discriminant. $)
    rmspecnonsq $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. ( NN \ []NN )
        ) $=
      ( va c2 cfv wcel cexp co c1 cn csquarenn wn cdif cz cc0 clt wbr a1i cr cq
      csqr cuz cmin cn0 2nn0 eluznn0 mpan nn0z zsqcl 3syl 1z zsubcl syl2anc sq1
      eluz2b2 simprbi cle 1re 1nn0 nn0ge0i eluzelre nn0ge0 lt2sq syl22anc mpbid
      wb syl syl5eqbrr nn0re resqcl posdif elnnz sylanbrc wa rmspecsqrnq eldifn
      cc intnand crab df-squarenn eleq2i fveq2 eleq1d elrab bitr2i sylnib eldif
      cv wceq ) ACUADEZACFGZHUBGZIEZWKJEZKWKIJLEWIWKMEZNWKOPZWLWIWJMEZHMEZWNWIA
      UCEZAMEWPCUCEWIWRUDACUEUFZAUGAUHUIWQWIUJQWJHUKULWIHWJOPZWOWIHHCFGZWJOUMWI
      HAOPZXAWJOPZWIAIEXBAUNUOWIHREZNHUPPZAREZNAUPPZXBXCVEXDWIUQQZXEWIHURUSQCAU
      TWIWRXGWSAVAVFHAVBVCVDVGWIXDWJREZWTWOVEXHWIWRXFXIWSAVHAVIUIHWJVJULVDWKVKV
      LWIWLWKTDZSEZVMZWMWIXKWLWIXJVPSLEXKKAVNXJVPSVOVFVQWMWKBWGZTDZSEZBIVRZEXLJ
      XPWKBVSVTXOXKBWKIXMWKWHXNXJSXMWKTWAWBWCWDWEWKIJWFVL $.
      $( [21-Sep-2014] $)
  $}

  $( This lemma implements the concept of "equate rational and irrational
     parts", used to prove many arithmetical properties of the X and Y
     sequences. $)
  qirropth $p |- ( ( A e. ( CC \ QQ ) /\ ( B e. QQ /\ C e. QQ ) /\ ( D e. QQ /\
      E e. QQ ) ) -> ( ( B + ( A x. C ) ) = ( D + ( A x. E ) ) <-> ( B = D /\ C
      = E ) ) ) $=
    ( cc cq wcel wa cmul co caddc wceq adantr cmin syl ad2antrr qcn syl2anc wb
    cdif w3a wn eldifn 3ad2ant1 cdiv simpll1 eldifi simp2r simp3r subdi syl3anc
    qsubcl mulcom simplr simp2l mulcl simp3l addsubeq4 syl22anc 3eqtr4d cc0 wne
    mpbid subeq0 necon3abid mpbird divmul syl112anc qdivcl eqeltrrd mt3d eqcomd
    simpr ex oveq2d eqtrd simpl2l simpl3l simpl1 simpl3r addcan2 jcai ancomd id
    oveq2 oveqan12d impbid1 ) AFGUAHZBGHZCGHZIZDGHZEGHZIZUBZBACJKZLKZDAEJKZLKZM
    ZBDMZCEMZIZWPXAXDWPXAIZXCXBXEXCXBXEXCAGHZWPXFUCZXAWIWLXGWOAFGUDUENXEXCUCZXF
    XEXHIZDBOKZCEOKZUFKZAGXIXLAMZXKAJKZXJMZXIAXKJKZWQWSOKZXNXJXIAFHZCFHZEFHZXPX
    QMXIWIXRWIWLWOXAXHUGAFGUHZPZXIWKXSWPWKXAXHWIWJWKWOUIQZCRPZXIWNXTWPWNXAXHWIW
    LWMWNUJQZERZPZACEUKULXIXKFHZXRXNXPMXIXKGHZYHXIWKWNYIYCYECEUMSZXKRPZYBXKAUNS
    XIXAXJXQMZWPXAXHUOXIBFHZWQFHZDFHZWSFHZXAYLTXIWJYMWPWJXAXHWIWJWKWOUPQZBRZPXI
    XRXSYNYBYDACUQSXIWMYOWPWMXAXHWIWLWMWNURQZDRZPXIXRXTYPYBYGAEUQZSBWQDWSUSUTVD
    VAXIXJFHZXRYHXKVBVCZXMXOTXIXJGHZUUBXIWMWJUUDYSYQDBUMSZXJRPYBYKXIUUCXHXEXHVN
    XIXSXTUUCXHTYDYGXSXTIXCXKVBCEVEVFSVGZXJAXKVHVIVGXIUUDYIUUCXLGHUUEYJUUFXJXKV
    JULVKVOVLXEXCXBXEXCIZBWSLKZWTMZXBUUGUUHWRWTUUGWSWQBLUUGECAJUUGCEXEXCVNVMVPV
    PWPXAXCUOVQUUGYMYOYPUUIXBTXEYMXCXEWJYMWJWKWIWOXAVRYRPNXEYOXCXEWMYOWMWNWIWLX
    AVSYTPNXEYPXCXEXRXTYPXEWIXRWIWLWOXAVTYAPXEWNXTWMWNWIWLXAWAYFPUUASNBDWSWBULV
    DVOWCWDVOXBXCBDWQWSLXBWECEAJWFWGWH $.
    $( [21-Sep-2014] $)

  $( The base of exponent used to define the X and Y sequences is the
     fundamental solution of the corresponding Pell equation. $)
  rmspecfund $p |- ( A e. ( ZZ>= ` 2 ) -> ( PellFund ` ( ( A ^ 2 ) - 1 ) ) = (
      A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ) $=
    ( c2 cfv wcel co c1 cmin csqr caddc wceq cle wbr cr wb syl clt syl2anc cmul
    a1i cc cuz cexp cpellfund wa csquarenn cdif rmspecnonsq pellfundre eluzelre
    cn crp cc0 cz eluzelz zre 3syl 1re resubcl sq1 eluz2b2 simprbi 1nn0 nn0ge0i
    zsqcl cn0 2nn0 eluznn0 nn0ge0 lt2sq syl22anc mpbid eqbrtrrd posdif sylanbrc
    mpan elrp rpsqrcl readdcl letri3 cpell14qr recnd mulid1 oveq2d cpell1qr wss
    pell1qrss14 oveq2i syl5eq ax-1cn nncan eqtrd pellqrexplicit syl31anc sseldd
    rpre eqeltrrd ltaddrp ltadd1 lttrd pellfundlb npcan fveq2d sqrsq pellfundge
    syl3anc oveq1d mpbir2and ) ABUACDZABUBEZFGEZUCCZAXJHCZIEZJZXKXMKLZXMXKKLZXH
    XKMDZXMMDZXNXOXPUDNXHXJUJUEUFDZXQAUGZXJUHOXHAMDZXLMDZXRBAUIZXHXLUKDZYBXHXJU
    KDZYDXHXJMDZULXJPLZYEXHXIMDZFMDZYFXHAUMDXIUMDYHBAUNAVDXIUOUPZYIXHUQSZXIFURQ
    ZXHFXIPLZYGXHFBUBEZFXIPYNFJXHUSSXHFAPLZYNXIPLZXHAUJDYOAUTVAZXHYIULFKLZYAULA
    KLZYOYPNYKYRXHFVBVCSYCXHAVEDZYSBVEDXHYTVFABVGVOZAVHOZFAVIVJVKVLXHYIYHYMYGNY
    KYJFXIVMQVKXJVPVNXJVQOZXLWOOZAXLVRQZXKXMVSQXHXSXMXJVTCZDFXMPLXOXTXHAXLFREZI
    EZXMUUFXHUUGXLAIXHXLTDUUGXLJXHXLUUDWAXLWBOWCXHXJWDCZUUFUUHXHXSUUIUUFWEXTXJW
    FOXHXSYTFVEDZXIXJYNREZGEZFJUUHUUIDXTUUAUUJXHVBSXHUULXIXJGEZFXHUUKXJXIGXHUUK
    XJFREZXJYNFXJRUSWGXHXJTDUUNXJJXHXJYLWAXJWBOWHWCXHXITDZFTDZUUMFJXHXIYJWAZUUP
    XHWISZXIFWJQWKAFXJWLWMWNWPXHFFXLIEZXMYKXHYIYBUUSMDYKUUDFXLVRQUUEXHYIYDFUUSP
    LYKUUCFXLWQQXHYOUUSXMPLZYQXHYIYAYBYOUUTNYKYCUUDFAXLWRXEVKWSXMXJWTXEXHXJFIEZ
    HCZXLIEZXMXKKXHUVBAXLIXHUVBXIHCZAXHUVAXIHXHUUOUUPUVAXIJUUQUURXIFXAQXBXHYAYS
    UVDAJYCUUBAXCQWKXFXHXSUVCXKKLXTXJXDOVLXG $.
    $( [21-Sep-2014] $)

  ${
    $d A a c d $.  $d N a $.
    $( The solutions used to construct the X and Y sequences are quadratic
       irrationals. $)
    rmxyelqirr $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A + ( sqr ` ( (
        A ^ 2 ) - 1 ) ) ) ^ N ) e. { a | E. c e. NN0 E. d e. ZZ a = ( c + ( (
        sqr ` ( ( A ^ 2 ) - 1 ) ) x. d ) ) } ) $=
      ( c2 cfv wcel cz wa cexp co cv wceq wrex cn0 cr crab cvv wss c1 cpell14qr
      cuz cmin csqr cmul caddc cn csquarenn cdif rmspecnonsq adantr pell14qrval
      cab syl wral simpl reximi rgenw a1i ss2rab sylibr ssv rabss2 ax-mp syl6ss
      wi rabab syl6sseq eqsstrd cpellfund simpr rmspecfund eqcomd oveq1d eqeq2d
      oveq2 rcla4ev syl2anc wb pellfund14b mpbird sseldd ) AFUCGHZBIHZJZAFKLUAU
      DLZUBGZCMZDMZWGUEGZEMZUFLUGLNZEIOZDPOZCUNZAWKUGLZBKLZWFWHWMWJFKLWGWLFKLUF
      LUDLUANZJZEIOZDPOZCQRZWPWFWGUHUIUJHZWHXCNWDXDWEAUKULZCDEWGUMUOWFXCWOCSRZW
      PWFXCWOCQRZXFWFXBWOVGZCQUPZXCXGTXIWFXHCQXAWNDPWTWMEIWMWSUQURURUSUTXBWOCQV
      AVBQSTXGXFTQVCWOCQSVDVEVFWOCVHVIVJWFWRWHHZWRWGVKGZWIKLZNZCIOZWFWEWRXKBKLZ
      NZXNWDWEVLWFWQXKBKWFXKWQWDXKWQNWEAVMULVNVOXMXPCBIWIBNXLXOWRWIBXKKVQVPVRVS
      WFXDXJXNVTXECWRWGWAUOWBWC $.
      $( [21-Sep-2014] $)
  $}

  ${
    $d b c d a A $.
    $( The function used to extract rational and irrational parts in ~ df-rmx
       and ~ df-rmy in fact achieves a one-to-one mapping from the quadratic
       irrationals to pairs of integers. $)
    rmxypairf1o $p |- ( A e. ( ZZ>= ` 2 ) -> ( b e. ( NN0 X. ZZ ) |-> ( ( 1st `
        b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) : ( NN0 X. ZZ
        ) -1-1-onto-> { a | E. c e. NN0 E. d e. ZZ a = ( c + ( ( sqr ` ( ( A ^
        2 ) - 1 ) ) x. d ) ) } ) $=
      ( cfv wcel cn0 cz cv c1st co c2nd cmul caddc wceq a1i fveq2 cq 3syl c2 c1
      cuz cxp cexp cmin csqr cmpt wfn crn wrex cab weq wral wf1o cvv eqid fnmpt
      wi ovex mprg rnmpt cop vex op1st syl6eq op2nd oveq2d oveq12d eqeq2d rexxp
      wb bicomi abbidv eqtr4d wa fvmpt ad2antrl ad2antll eqeq12d cc rmspecsqrnq
      cdif adantr simprl xp1st nn0ssq sseli zq simprr qirropth syl122anc biimpd
      xp2nd xpopth adantl sylibd sylbid ralrimivva w3a dff1o6 biimpri syl3anc )
      AUAUCFGZCHIUDZCJZKFZAUAUELUBUFLUGFZXFMFZNLZOLZUHZXEUIZXLUJZBJZDJZXHEJZNLZ
      OLZPZEIUKDHUKZBULZPZXPXLFZXQXLFZPZDEUMZUSZEXEUNDXEUNZXEYBXLUOZXMXDXKUPGZX
      MCXECXEXKXLUPXLUQZURYKXFXEGXGXJOUTQVAQXDXNXOXKPZCXEUKZBULZYBXNYOPXDCBXEXK
      XLYLVBQXDYAYNBYAYNVLXDYNYAYMXTCDEHIXFXPXQVCZPZXKXSXOYQXGXPXJXROYQXGYPKFXP
      XFYPKRXPXQDVDZVEVFYQXIXQXHNYQXIYPMFXQXFYPMRXPXQYREVDVGVFVHVIVJVKVMQVNVOXD
      YHDEXEXEXDXPXEGZXQXEGZVPZVPZYFXPKFZXHXPMFZNLZOLZXQKFZXHXQMFZNLZOLZPZYGUUB
      YDUUFYEUUJYSYDUUFPXDYTCXPXKUUFXEXLCDUMZXGUUCXJUUEOXFXPKRUULXIUUDXHNXFXPMR
      VHVIYLUUCUUEOUTVQVRYTYEUUJPXDYSCXQXKUUJXEXLCEUMZXGUUGXJUUIOXFXQKRUUMXIUUH
      XHNXFXQMRVHVIYLUUGUUIOUTVQVSVTUUBUUKUUCUUGPUUDUUHPVPZYGUUBUUKUUNUUBXHWASW
      CGZUUCSGZUUDSGZUUGSGZUUHSGZUUKUUNVLXDUUOUUAAWBWDUUBYSUUCHGUUPXDYSYTWEZXPH
      IWFHSUUCWGWHTUUBYSUUDIGUUQUUTXPHIWNUUDWITUUBYTUUGHGUURXDYSYTWJZXQHIWFHSUU
      GWGWHTUUBYTUUHIGUUSUVAXQHIWNUUHWITXHUUCUUDUUGUUHWKWLWMUUAUUNYGVLXDXPXQHIH
      IWOWPWQWRWSYJXMYCYIWTDEXEYBXLXAXBXC $.
      $( [21-Sep-2014] $)
  $}

  ${
    $d a b c d A $.  $d a N $.
    $( Lemma for ~ frmx and ~ frmy . $)
    rmxyelxp $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( `' ( b e. ( NN0 X.
        ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) )
        ) ) ` ( ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) ) e. ( NN0 X. ZZ ) )
        $=
      ( va vc vd c2 cuz cfv wcel cz wa cn0 cxp cv cexp co cmul caddc wrex cmin
      c1 csqr wceq cab c1st c2nd cmpt wf1o ccnv rmxypairf1o rmxyelqirr f1ocnvdm
      adantr syl2anc ) AGHIJZBKJZLMKNZDOEOAGPQUBUAQUCIZFORQSQUDFKTEMTDUEZCURCOZ
      UFIUSVAUGIRQSQUHZUIZAUSSQBPQZUTJVDVBUJIURJUPVCUQADCEFUKUNABDEFULURUTVDVBU
      MUO $.
      $( [22-Sep-2014] $)
  $}

  ${
    $d a b c $.
    $( The X sequence is a nonnegative integer.  See ~ rmxnn for a
       strengthening. $)
    frmx $p |- rmX : ( ( ZZ>= ` 2 ) X. ZZ ) --> NN0 $=
      ( va vb vc cv c2 cexp co c1 cmin csqr cfv caddc cn0 cz cxp c1st c2nd wcel
      wral crmx cmul cmpt ccnv cuz wf wa rmxyelxp xp1st rgen2 df-rmx fmpt2 mpbi
      syl ) ADZUNEFGHIGJKZLGBDZFGCMNOZCDZPKUOURQKUAGLGUBUCKZPKZMRZBNSAEUDKZSVBN
      OMTUEVAABVBNUNVBRUPNRUFUSUQRVAUNUPCUGUSMNUHUMUIABVBNUTMTBACUJUKUL $.
      $( [22-Sep-2014] $)

    $( The Y sequence is an integer. $)
    frmy $p |- rmY : ( ( ZZ>= ` 2 ) X. ZZ ) --> ZZ $=
      ( va vb vc cv c2 cexp co c1 cmin csqr cfv caddc cn0 cz cxp c1st c2nd wcel
      wral crmy cmul cmpt ccnv cuz wf wa rmxyelxp xp2nd rgen2 df-rmy fmpt2 mpbi
      syl ) ADZUNEFGHIGJKZLGBDZFGCMNOZCDZPKUOURQKUAGLGUBUCKZQKZNRZBNSAEUDKZSVBN
      ONTUEVAABVBNUNVBRUPNRUFUSUQRVAUNUPCUGUSMNUHUMUIABVBNUTNTBACUJUKUL $.
      $( [22-Sep-2014] $)
  $}

  ${
    $d a b c d A $.  $d a b c N $.
    $( Main definition of the X and Y sequences, for instance
       [JonesMatijasevic] 2.3. $)
    rmxyval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmX N ) + ( ( sqr
        ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) ) = ( ( A + ( sqr ` ( ( A ^ 2 )
        - 1 ) ) ) ^ N ) ) $=
      ( vb va vc vd c2 cfv wcel cz co cmul caddc c1st c2nd oveq2d oveq12d fveq2
      cv wceq cuz wa crmx cexp cmin csqr crmy cn0 cxp cmpt ccnv rmxfval rmyfval
      c1 rmxyelxp weq cbvmptv ovex fvmpt syl wrex rmxypairf1o adantr rmxyelqirr
      cab wf1o f1ocnvfv2 syl2anc 3eqtr2d ) AGUAHIZBJIZUBZABUCKZAGUDKUNUEKUFHZAB
      UGKZLKZMKAVNMKBUDKZCUHJUIZCSZNHZVNVSOHZLKZMKZUJZUKHZNHZVNWEOHZLKZMKZWEWDH
      ZVQVLVMWFVPWHMABCULVLVOWGVNLABCUMPQVLWEVRIWJWITABCUODWEDSZNHZVNWKOHZLKZMK
      ZWIVRWDWKWETZWLWFWNWHMWKWENRWPWMWGVNLWKWEORPQCDVRWCWOCDUPZVTWLWBWNMVSWKNR
      WQWAWMVNLVSWKORPQUQWFWHMURUSUTVLVRWKESVNFSLKMKTFJVAEUHVADVEZWDVFZVQWRIWJV
      QTVJWSVKADCEFVBVCABDEFVDVRWRVQWDVGVHVI $.
      $( [19-Oct-2014] $)
  $}

  $( The discriminant used to define the X and Y sequences is a positive
     real. $)
  rmspecpos $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. RR+ ) $=
    ( c2 cuz cfv wcel cexp co c1 cmin cr cc0 clt wbr crp cn0 a1i syl2anc cle wb
    mpbid 2nn0 eluznn0 mpan resqcl 3syl 1re resubcl sq1 cz eluz2b1 simprbi 1nn0
    nn0re nn0ge0i eluzelre nn0ge0 lt2sq syl22anc syl5eqbrr posdif elrp sylanbrc
    syl ) ABCDEZABFGZHIGZJEZKVFLMZVFNEVDVEJEZHJEZVGVDAOEZAJEZVIBOEVDVKUAABUBUCZ
    AUMAUDUEZVJVDUFPZVEHUGQVDHVELMZVHVDHHBFGZVELUHVDHALMZVQVELMZVDAUIEVRAUJUKVD
    VJKHRMZVLKARMZVRVSSVOVTVDHULUNPBAUOVDVKWAVMAUPVCHAUQURTUSVDVJVIVPVHSVOVNHVE
    UTQTVFVAVB $.
    $( [22-Sep-2014] $)

  ${
    $d A n $.  $d X n $.  $d Y n $.  $d X x y $.  $d Y x y $.  $d A x y $.
    $( The X and Y sequences taken together enumerate all solutions to the
       corresponding Pell equation in the right half-plane. $)
    rmxycomplete $p |- ( ( A e. ( ZZ>= ` 2 ) /\ X e. NN0 /\ Y e. ZZ ) -> ( ( (
        X ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( Y ^ 2 ) ) ) = 1 <-> E. n e. ZZ ( X =
        ( A rmX n ) /\ Y = ( A rmY n ) ) ) ) $=
      ( vx vy c2 wcel cn0 cz cexp co c1 cmin cmul caddc wceq wa cq adantr cv cn
      cuz cfv w3a csqr cpell14qr cpellfund wrex crmx crmy csquarenn rmspecnonsq
      cdif wb 3ad2ant1 pellfund14b syl cr nn0re 3ad2ant2 rmspecpos rpsqrcl rpre
      crp 3syl zre 3ad2ant3 remulcl syl2anc biantrurd simpl2 simpl3 eqidd simpr
      readdcl oveq1 eqeq2d oveq1d eqeq1d anbi12d oveq2 rcla42ev syl112anc ex cc
      oveq2d rmspecsqrnq nn0ssq simp2 sseldi zq sseli ad2antrl syl122anc biimpd
      ad2antll anim1d oveqan12d eqcomd biimpa syl6 rexlimdvva impbid elpell14qr
      qirropth 3bitr4d cxp wf frmx a1i simpl1 fovrn syl3anc zssq frmy 3ad2antl1
      rmxyval rmspecfund eqtr4d bitr3d rexbidva ) AGUCUDZHZCIHZDJHZUEZCAGKLMNLZ
      UFUDZDOLZPLZYHUGUDHZYKYHUHUDZBUAZKLZQZBJUIZCGKLZYHDGKLZOLZNLZMQZCAYNUJLZQ
      DAYNUKLZQRZBJUIYGYHUBULUNHZYLYQUOYDYEUUFYFAUMUPZBYKYHUQURYGYKEUAZYIFUAZOL
      ZPLZQZUUHGKLZYHUUIGKLZOLZNLZMQZRZFJUIEIUIZYKUSHZUUSRZUUBYLYGUUTUUSYGCUSHZ
      YJUSHZUUTYEYDUVBYFCUTVAYGYIUSHZDUSHZUVCYDYEUVDYFYDYHVEHYIVEHUVDAVBYHVCYIV
      DVFUPYFYDUVEYEDVGVHYIDVIVJCYJVPVJVKYGUUBUUSYGUUBUUSYGUUBRZYEYFYKYKQZUUBUU
      SYDYEYFUUBVLYDYEYFUUBVMUVFYKVNYGUUBVOUURUVGUUBRYKCUUJPLZQZYRUUONLZMQZREFC
      DIJUUHCQZUULUVIUUQUVKUVLUUKUVHYKUUHCUUJPVQVRUVLUUPUVJMUVLUUMYRUUONUUHCGKV
      QVSVTWAUUIDQZUVIUVGUVKUUBUVMUVHYKYKUVMUUJYJCPUUIDYIOWBWGVRUVMUVJUUAMUVMUU
      OYTYRNUVMUUNYSYHOUUIDGKVQWGWGVTWAWCWDWEYGUURUUBEFIJYGUUHIHZUUIJHZRZRZUURC
      UUHQZDUUIQZRZUUQRUUBUVQUULUVTUUQUVQUULUVTUVQYIWFSUNHZCSHZDSHZUUHSHZUUISHZ
      UULUVTUOYGUWAUVPYDYEUWAYFAWHUPZTYGUWBUVPYGISCWIYDYEYFWJWKZTYGUWCUVPYFYDUW
      CYEDWLVHZTUVNUWDYGUVOISUUHWIWMWNUVOUWEYGUVNUUIWLWQYICDUUHUUIXFWOWPWRUVTUU
      QUUBUVTUUPUUAMUVTUUAUUPUVRUVSYRUUMYTUUONCUUHGKVQUVSYSUUNYHODUUIGKVQWGWSWT
      VTXAXBXCXDYGUUFYLUVAUOUUGEFYKYHXEURXGYGUUEYPBJYGYNJHZRZYKUUCYIUUDOLPLZQZU
      UEYPUWJUWAUWBUWCUUCSHUUDSHUWLUUEUOYGUWAUWIUWFTYGUWBUWIUWGTYGUWCUWIUWHTUWJ
      ISUUCWIUWJYCJXHZIUJXIZYDUWIUUCIHUWNUWJXJXKYDYEYFUWIXLZYGUWIVOZAYNIYCJUJXM
      XNWKUWJJSUUDXOUWJUWMJUKXIZYDUWIUUDJHUWQUWJXPXKUWOUWPAYNJYCJUKXMXNWKYICDUU
      CUUDXFWOUWJUWKYOYKUWJUWKAYIPLZYNKLZYOYDYEUWIUWKUWSQYFAYNXRXQUWJYMUWRYNKYG
      YMUWRQZUWIYDYEUWTYFAXSUPTVSXTVRYAYBXG $.
      $( [22-Sep-2014] $)
  $}

  ${
    $d A a $.  $d N a $.
    $( The X and Y sequences define a solution to the corresponding Pell
       equation. $)
    rmxynorm $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( ( A rmX N ) ^ 2 )
        - ( ( ( A ^ 2 ) - 1 ) x. ( ( A rmY N ) ^ 2 ) ) ) = 1 ) $=
      ( va c2 cuz wcel cz wa crmx co cexp cmin crmy wceq eqidd oveq2 eqeq2d cn0
      c1 fovcl cmul cv wrex simpr anim12i anbi12d rcla4ev syl2anc wb simpl frmx
      cfv frmy rmxycomplete syl3anc mpbird ) ADEULZFZBGFZHZABIJZDKJADKJSLJABMJZ
      DKJUAJLJSNZVAACUBZIJZNZVBAVDMJZNZHZCGUCZUTUSVAVANZVBVBNZHZVJURUSUDURVKUSV
      LURVAOUSVBOUEVIVMCBGVDBNZVFVKVHVLVNVEVAVAVDBAIPQVNVGVBVBVDBAMPQUFUGUHUTUR
      VARFVBGFVCVJUIURUSUJABRUQGIUKTABGUQGMUMTACVAVBUNUOUP $.
      $( [22-Sep-2014] $)
  $}

  $( The base of exponentiation for the X and Y sequences is a positive
     real. $)
  rmbaserp $p |- ( A e. ( ZZ>= ` 2 ) -> ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) e.
      RR+ ) $=
    ( c2 cuz cfv wcel cexp co c1 cmin cpellfund csqr caddc rmspecfund csquarenn
    crp cn cdif rmspecnonsq pellfundrp syl eqeltrrd ) ABCDEZABFGHIGZJDZAUCKDLGO
    AMUBUCPNQEUDOEARUCSTUA $.
    $( [22-Sep-2014] $)

  $( Negation law for X and Y sequences.  [JonesMatijasevic] is inconsistent on
     whether the X and Y sequences have domain ` NN0 ` or ` ZZ ` ; we use
     ` ZZ ` consistently to avoid the need for a separate subtraction law. $)
  rmxyneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmX -u N ) = ( A
      rmX N ) /\ ( A rmY -u N ) = -u ( A rmY N ) ) ) $=
    ( c2 wcel cz crmx co cexp c1 cmin crmy cmul caddc cc syl sseldi syl2anc cn0
    wceq cq cuz cfv wa cneg csqr cdiv znegcl rmxyval sylan2 cc0 rmbaserp adantr
    wne crp rpcn rpne0 simpr expnegz syl3anc cn csquarenn cdif rmspecnonsq nncn
    eldifi 3syl sqrcl zsscn frmy fovcl mulneg2 oveq2d nn0sscn frmx mulcl negsub
    eqtrd subsq sqmul sqrth oveq1d 3eqtr2d expclz eqeltrd expne0i eqnetrd recid
    rmxynorm eqtr4d negcl addcl reccl mulcan syl112anc mpbid eqtr2d rmspecsqrnq
    wb 3eqtrd nn0ssq zssq qnegcl qirropth syl122anc ) ACUAUBZDZBEDZUCZABUDZFGZA
    CHGIJGZUEUBZAXIKGZLGMGZABFGZXLABKGZUDZLGZMGZSZXJXOSXMXQSUCZXHXNAXLMGZXIHGZI
    YBBHGZUFGZXSXGXFXIEDZXNYCSBUGZAXIUHUIXHYBNDZYBUJUMZXGYCYESXFYHXGXFYBUNDZYHA
    UKZYBUOOULZXFYIXGXFYJYIYKYBUPOULZXFXGUQZYBBURUSXHXSIXOXLXPLGZMGZUFGZYEXHYPX
    SLGZYPYQLGZSZXSYQSZXHYRIYSXHYRYPXOYOJGZLGZXOCHGZYOCHGZJGZIXHXSUUBYPLXHXSXOY
    OUDZMGZUUBXHXRUUGXOMXHXLNDZXPNDZXRUUGSXHXKNDZUUIXFUUKXGXFXKUTVAVBDXKUTDUUKA
    VCXKUTVAVEXKVDVFULZXKVGOZXHENXPVHABEXEEKVIVJZPZXLXPVKQVLXHXONDZYONDZUUHUUBS
    XHRNXOVMABRXEEFVNVJZPZXHUUIUUJUUQUUMUUOXLXPVOQZXOYOVPQVQVLXHUUPUUQUUFUUCSUU
    SUUTXOYOVRQXHUUFUUDXKXPCHGZLGZJGIXHUUEUVBUUDJXHUUEXLCHGZUVALGZUVBXHUUIUUJUU
    EUVDSUUMUUOXLXPVSQXHUVCXKUVALXHUUKUVCXKSUULXKVTOWAVQVLABWHVQWBXHYPNDZYPUJUM
    ZYSISXHYPYDNABUHZXHYHYIXGYDNDYLYMYNYBBWCUSWDZXHYPYDUJUVGXHYHYIXGYDUJUMYLYMY
    NYBBWEUSWFZYPWGQWIXHXSNDZYQNDZUVEUVFYTUUAWRXHUUPXRNDZUVJUUSXHUUIXQNDZUVLUUM
    XHUUJUVMUUOXPWJOXLXQVOQXOXRWKQXHUVEUVFUVKUVHUVIYPWLQUVHUVIXSYQYPWMWNWOXHYPY
    DIUFUVGVLWPWSXHXLNTVBDZXJTDXMTDXOTDXQTDZXTYAWRXFUVNXGAWQULXHRTXJWTXGXFYFXJR
    DYGAXIRXEEFVNVJUIPXHETXMXAXGXFYFXMEDYGAXIEXEEKVIVJUIPXHRTXOWTUURPXHXPTDUVOX
    HETXPXAUUNPXPXBOXLXJXMXOXQXCXDWO $.
    $( [22-Sep-2014] $)

  $( Addition formula for X and Y sequences.  See ~ rmxadd and ~ rmyadd for
     most uses. $)
  rmxyadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> (
        ( A rmX ( M + N ) ) = ( ( ( A rmX M ) x. ( A rmX N ) ) + ( ( ( A ^ 2 )
      - 1 ) x. ( ( A rmY M ) x. ( A rmY N ) ) ) ) /\
        ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M )
      x. ( A rmY N ) ) ) ) ) $=
    ( wcel cz caddc co crmx cexp crmy cmul wceq syl2anc cc cq cn0 fovrn syl3anc
    sseldi qmulcl c2 cuz cfv w3a c1 cmin csqr wa zaddcl 3adant1 rmxyval cc0 wne
    simp1 eluzelz 3ad2ant1 zcn syl zq qsqcl 3syl 1z sselii a1i qsubcl qcn sqrcl
    zssq addcl crp rmbaserp rpne0 simp2 simp3 expaddz syl22anc qsscn nn0ssq cxp
    frmx frmy mulcl muladd oveq12d mul4 sqval rmspecpos rpcn sqrth eqtr3d eqtrd
    wf mulcom oveq2d mul12 adddi addcom oveq1d 3eqtr2d 3eqtr3d cdif rmspecsqrnq
    3eqtrd wb qaddcl qirropth syl122anc mpbid ) AUAUBUCZDZBEDZCEDZUDZABCFGZHGZA
    UAIGZUEUFGZUGUCZAXNJGZKGFGZABHGZACHGZKGZXQABJGZACJGZKGZKGZFGZXRYDYBKGZYAYEK
    GZFGZKGZFGZLZXOYHLXSYKLUHZXMXTAXRFGZXNIGZYPBIGZYPCIGZKGZYMXMXJXNEDZXTYQLXJX
    KXLUNZXKXLUUAXJBCUIUJZAXNUKMXMYPNDZYPULUMZXKXLYQYTLXMANDZXRNDZUUDXMAEDZUUFX
    JXKUUHXLUAAUOUPZAUQURXMXQODZXQNDZUUGXMXPODZUEODZUUJXMUUHAODUULUUIAUSAUTVAUU
    MXMEOUEVHVBVCVDXPUEVEMZXQVFXQVGVAZAXRVIMXJXKUUEXLXJYPVJDUUEAVKYPVLURUPXJXKX
    LVMZXJXKXLVNZYPBCVOVPXMYAXRYDKGZFGZYBXRYEKGZFGZKGZYCUUTUURKGZFGZYAUUTKGZYBU
    URKGZFGZFGZYTYMXMYANDZUURNDZYBNDZUUTNDZUVBUVHLXMONYAVQXMPOYAVRXMXIEVSZPHWLZ
    XJXKYAPDUVNXMVTVDZUUBUUPABPXIEHQRSZSZXMUUGYDNDZUVJUUOXMONYDVQXMEOYDVHXMUVME
    JWLZXJXKYDEDUVSXMWAVDZUUBUUPABEXIEJQRSZSZXRYDWBMXMONYBVQXMPOYBVRXMUVNXJXLYB
    PDUVOUUBUUQACPXIEHQRSZSZXMUUGYENDZUVLUUOXMONYEVQXMEOYEVHXMUVSXJXLYEEDUVTUUB
    UUQACEXIEJQRSZSZXRYEWBMYAUURYBUUTWCVPXMUUSYRUVAYSKXMXJXKUUSYRLUUBUUPABUKMXM
    XJXLUVAYSLUUBUUQACUKMWDXMUVDYHUVGYLFXMUVCYGYCFXMUVCXRXRKGZYEYDKGZKGZYGXMUUG
    UWEUUGUVRUVCUWJLUUOUWGUUOUWBXRYEXRYDWEVPXMUWHXQUWIYFKXMXRUAIGZUWHXQXMUUGUWK
    UWHLUUOXRWFURXMXQVJDZUUKUWKXQLXJXKUWLXLAWGUPXQWHXQWIVAWJXMUWEUVRUWIYFLUWGUW
    BYEYDWMMWDWKWNXMUVGXRYJKGZXRYBYDKGZKGZFGZXRYJUWNFGZKGZYLXMUVEUWMUVFUWOFXMUV
    IUUGUWEUVEUWMLUVQUUOUWGYAXRYEWORXMUVKUUGUVRUVFUWOLUWDUUOUWBYBXRYDWORWDXMUUG
    YJNDZUWNNDZUWRUWPLUUOXMUVIUWEUWSUVQUWGYAYEWBMZXMUVKUVRUWTUWDUWBYBYDWBMZXRYJ
    UWNWPRXMUWQYKXRKXMUWQUWNYJFGZYKXMUWSUWTUWQUXCLUXAUXBYJUWNWQMXMUWNYIYJFXMUVK
    UVRUWNYILUWDUWBYBYDWMMWRWKWNWSWDWTXCXMXRNOXADZXOODXSODYHODZYKODZYNYOXDXJXKU
    XDXLAXBUPXMPOXOVRXMUVNXJUUAXOPDUVOUUBUUCAXNPXIEHQRSXMEOXSVHXMUVSXJUUAXSEDUV
    TUUBUUCAXNEXIEJQRSXMYCODZYGODZUXEXMYAODZYBODZUXGUVPUWCYAYBTMXMUUJYFODZUXHUU
    NXMYDODZYEODZUXKUWAUWFYDYETMXQYFTMYCYGXEMXMYIODZYJODZUXFXMUXLUXJUXNUWAUWCYD
    YBTMXMUXIUXMUXOUVPUWFYAYETMYIYJXEMXRXOXSYHYKXFXGXH $.
    $( [22-Sep-2014] $)

  $( Value of the X and Y sequences at 1. $)
  rmxy1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A rmX 1 ) = A /\ ( A rmY 1 ) = 1 ) )
      $=
    ( c2 cfv wcel c1 crmx co cexp crmy cmul caddc wceq cz 1z mpan2 crp rpcn cn0
    cc cq cmin csqr wa rmxyval rmbaserp exp1 3syl rmspecpos sqrcl mulid1 eqcomd
    cuz oveq2d 3eqtrd cdif wb rmspecsqrnq nn0ssq frmx fovcl sseldi zssq eluzelz
    syl frmy zq sselii a1i qirropth syl122anc mpbid ) ABULCZDZAEFGZABHGEUAGZUBC
    ZAEIGZJGKGZAVPEJGZKGZLZVNALVQELUCZVMVRAVPKGZEHGZWCVTVMEMDZVRWDLNAEUDOVMWCPD
    WCSDWDWCLAUEWCQWCUFUGVMVPVSAKVMVSVPVMVPSDZVSVPLVMVOPDVOSDWFAUHVOQVOUIUGVPUJ
    VDUKUMUNVMVPSTUODVNTDVQTDATDZETDZWAWBUPAUQVMRTVNURVMWEVNRDNAERVLMFUSUTOVAVM
    MTVQVBVMWEVQMDNAEMVLMIVEUTOVAVMAMDWGBAVCAVFVDWHVMMTEVBNVGVHVPVNVQAEVIVJVK
    $.
    $( [22-Sep-2014] $)

  $( Value of the X and Y sequences at 0. $)
  rmxy0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A rmX 0 ) = 1 /\ ( A rmY 0 ) = 0 ) )
      $=
    ( c2 cfv wcel cc0 crmx co cexp c1 crmy cmul caddc wceq cz 0z mpan2 cn0 zssq
    cc cq cuz cmin csqr wa rmxyval crp rmbaserp rpcn exp0 rmspecpos sqrcl mul01
    3syl syl oveq2d ax-1cn addid1i syl6req 3eqtrd cdif rmspecsqrnq nn0ssq fovcl
    wb frmx sseldi frmy 1z sselii a1i qirropth syl122anc mpbid ) ABUACZDZAEFGZA
    BHGIUBGZUCCZAEJGZKGLGZIVREKGZLGZMZVPIMVSEMUDZVOVTAVRLGZEHGZIWBVOENDZVTWFMOA
    EUEPVOWEUFDWESDWFIMAUGWEUHWEUIUMVOWBIELGIVOWAEILVOVRSDZWAEMVOVQUFDVQSDWHAUJ
    VQUHVQUKUMVRULUNUOIUPUQURUSVOVRSTUTDVPTDVSTDITDZETDZWCWDVDAVAVOQTVPVBVOWGVP
    QDOAEQVNNFVEVCPVFVONTVSRVOWGVSNDOAENVNNJVGVCPVFWIVONTIRVHVIVJWJVONTEROVIVJV
    RVPVSIEVKVLVM $.
    $( [22-Sep-2014] $)

  $( Negation law (even function) for the X sequence.  The method of proof used
     for the previous four theorems ~ rmxyneg , ~ rmxyadd , ~ rmxy0 , and
     ~ rmxy1 via ~ qirropth results in two theorems at once, but typical use
     requires only one, so this group of theorems serves to separate the
     cases. $)
  rmxneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX -u N ) = ( A rmX N
      ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simpld ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.
    $( [22-Sep-2014] $)

  $( Value of X sequence at 0.  [JonesMatijasevic] 2.11 #1 $)
  rmx0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 0 ) = 1 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simpld ) ABCDEAFGHIJAFKHFJ
    ALM $.
    $( [22-Sep-2014] $)

  $( Value of X sequence at 1.  [JonesMatijasevic] 2.11 #2 $)
  rmx1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 1 ) = A ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simpld ) ABCDEAFGHAIAFJHFIAKL
    $.
    $( [22-Sep-2014] $)

  $( Addition formula for X sequence.  [JonesMatijasevic] 2.7 $)
  rmxadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmX ( M + N ) ) = ( ( ( A rmX M ) x. ( A rmX N ) ) + ( ( ( A ^ 2 )
      - 1 ) x. ( ( A rmY M ) x. ( A rmY N ) ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simpld
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.
    $( [22-Sep-2014] $)

  $( Negation formula for Y sequence (odd function). $)
  rmyneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY -u N ) = -u ( A
      rmY N ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simprd ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.
    $( [22-Sep-2014] $)

  $( Value of Y sequence at 0.  [JonesMatijasevic] 2.12 #1 $)
  rmy0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 0 ) = 0 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simprd ) ABCDEAFGHIJAFKHFJ
    ALM $.
    $( [22-Sep-2014] $)

  $( Value of Y sequence at 1.  [JonesMatijasevic] 2.12 #2 $)
  rmy1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 1 ) = 1 ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simprd ) ABCDEAFGHAIAFJHFIAKL
    $.
    $( [22-Sep-2014] $)

  $( Addition formula for Y sequence.  [JonesMatijasevic] 2.8 $)
  rmyadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M )
      x. ( A rmY N ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simprd
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.
    $( [22-Sep-2014] $)

  $( Special addition-of-1 formula for X sequence.  [JonesMatijasevic] 2.9
     #1 $)
  rmxp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmX ( N + 1 ) ) = ( ( ( A rmX N ) x. A ) + ( ( ( A ^ 2 ) - 1 ) x. (
      A rmY N ) ) ) ) $=
    ( c2 cuz wcel cz wa c1 caddc co crmx cmul cexp cmin crmy wceq adantr oveq2d
    cfv eqtrd 1z rmxadd mp3an3 rmx1 rmy1 cc frmy fovcl zcn mulid1 3syl oveq12d
    ) ACDSZEZBFEZGZABHIJKJZABKJZAHKJZLJZACMJHNJZABOJZAHOJZLJZLJZIJZURALJZVAVBLJ
    ZIJUNUOHFEUQVFPUAABHUBUCUPUTVGVEVHIUPUSAURLUNUSAPUOAUDQRUPVDVBVALUPVDVBHLJZ
    VBUNVDVIPUOUNVCHVBLAUERQUPVBFEVBUFEVIVBPABFUMFOUGUHVBUIVBUJUKTRULT $.
    $( [19-Oct-2014] $)

  $( Special addition of 1 formula for Y sequence.  [JonesMatijasevic] 2.9
     #2 $)
  rmyp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmY ( N + 1 ) ) = ( ( ( A rmY N ) x. A ) + ( A rmX N ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc co crmy crmx cmul wceq oveq2d adantr eqtrd
    1z cn0 rmyadd mp3an3 rmx1 rmy1 cc frmx fovcl nn0cn mulid1 3syl oveq12d ) AC
    DEZFZBGFZHZABIJKLKZABLKZAIMKZNKZABMKZAILKZNKZJKZUQANKZUTJKUMUNIGFUPVCOSABIU
    AUBUOUSVDVBUTJUMUSVDOUNUMURAUQNAUCPQUOVBUTINKZUTUMVBVEOUNUMVAIUTNAUDPQUOUTT
    FUTUEFVEUTOABTULGMUFUGUTUHUTUIUJRUKR $.
    $( [24-Sep-2014] $)

  $( Subtraction of 1 formula for Y sequence.  [JonesMatijasevic] 2.10 #1 $)
  rmxm1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmX ( N - 1 ) ) = ( ( A x. ( A rmX N ) ) -
        ( ( ( A ^ 2 ) - 1 ) x. ( A rmY N ) ) ) ) $=
    ( c2 wcel cz c1 cneg caddc co crmx cmul cmin crmy wceq eqtrd adantr syl2anc
    oveq2d cc cn cuz cfv wa cexp 1nn0 nn0negzi rmxadd mp3an3 1z rmxneg rmx1 cn0
    mpan2 nn0sscn frmx fovcl sseldi eluzelz zcn mulcom rmyneg rmy1 negeqd zsscn
    frmy ax-1cn mulneg2 sylancl mulid1 3eqtrd csquarenn cdif rmspecnonsq eldifi
    syl nncn 3syl oveq12d adantl negsub mulcl 3eqtr3d ) ACUAUBZDZBEDZUCZABFGZHI
    ZJIZAABJIZKIZACUDIFLIZABMIZKIZGZHIZABFLIZJIWKWNLIZWFWIWJAWGJIZKIZWLWMAWGMIZ
    KIZKIZHIZWPWDWEWGEDWIXDNFUEUFABWGUGUHWFWTWKXCWOHWFWTWJAKIZWKWFWSAWJKWDWSANW
    EWDWSAFJIZAWDFEDZWSXFNUIAFUJUMAUKOPRWFWJSDZASDZXEWKNWFULSWJUNABULWCEJUOUPUQ
    ZWDXIWEWDAEDXICAURAUSVOPZWJAUTQOWFXCWLWMGZKIZWOWFXBXLWLKWFXBWMWGKIZWMFKIZGZ
    XLWDXBXNNWEWDXAWGWMKWDXAAFMIZGZWGWDXGXAXRNUIAFVAUMWDXQFAVBVCORPWFWMSDZFSDZX
    NXPNWFESWMVDABEWCEMVEUPUQZVFWMFVGVHWFXOWMWFXSXOWMNYAWMVIVOVCVJRWFWLSDZXSXMW
    ONWDYBWEWDWLTVKVLDWLTDYBAVMWLTVKVNWLVPVQPZYAWLWMVGQOVROWFWHWQAJWFBSDZXTWHWQ
    NWEYDWDBUSVSVFBFVTVHRWFWKSDZWNSDZWPWRNWFXIXHYEXKXJAWJWAQWFYBXSYFYCYAWLWMWAQ
    WKWNVTQWB $.
    $( [14-Oct-2014] $)

  $( Subtraction of 1 formula for Y sequence.  [JonesMatijasevic] 2.10 #1 $)
  rmym1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmY ( N - 1 ) ) = ( ( ( A rmY N ) x. A ) - ( A rmX N ) ) ) $=
    ( c2 wcel cz c1 cmin co crmy cneg caddc crmx cmul wceq ax-1cn negsub oveq2d
    cc eqtrd adantr cuz cfv wa zcn adantl sylancl eqcomd nn0negzi rmyadd mp3an3
    1nn0 1z rmxneg mpan2 rmx1 rmyneg rmy1 negeqd cn0 nn0sscn frmx sseldi negcli
    fovcl mulcom mulm1 3eqtrd oveq12d zsscn frmy eluzelre recnd mulcl syl2anc
    syl ) ACUAUBZDZBEDZUCZABFGHZIHABFJZKHZIHZABIHZAWALHZMHZABLHZAWAIHZMHZKHZWDA
    MHZWGGHZVSVTWBAIVSWBVTVSBRDZFRDWBVTNVRWMVQBUDUEOBFPUFUGQVQVRWAEDWCWJNFUKUHA
    BWAUIUJVSWJWKWGJZKHZWLVSWFWKWIWNKVSWEAWDMVQWEANVRVQWEAFLHZAVQFEDZWEWPNULAFU
    MUNAUOSTQVSWIWGWAMHZWAWGMHZWNVSWHWAWGMVQWHWANVRVQWHAFIHZJZWAVQWQWHXANULAFUP
    UNVQWTFAUQURSTQVSWGRDZWARDWRWSNVSUSRWGUTABUSVPELVAVDVBZFOVCWGWAVEUFVSXBWSWN
    NXCWGVFVOVGVHVSWKRDZXBWOWLNVSWDRDARDZXDVSERWDVIABEVPEIVJVDVBVQXEVRVQACAVKVL
    TWDAVMVNXCWKWGPVNSVG $.
    $( [19-Oct-2014] $)

  $( The X sequence is a Lucas (second-order integer recurrence) sequence.
     [JonesMatijasevic] 2.11 #3 $)
  rmxluc $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( N + 1 ) ) =
      ( ( ( 2 x. A ) x. ( A rmX N ) ) - ( A rmX ( N - 1 ) ) ) ) $=
    ( c2 wcel cz wa cmul co crmx c1 cmin caddc wceq cc cn0 nn0sscn fovcl sseldi
    syl2anc mulcl cuz cexp crmy peano2zm frmx sylan2 peano2z addcom rmxp1 rmxm1
    cfv oveq12d eluzelz zcn syl adantr cn csquarenn cdif rmspecnonsq nncn zsscn
    eldifi 3syl ppncan syl3anc mulcom oveq1d 2cn mulass 2times eqtr2d 3eqtrd wb
    frmy a1i sylancr subadd mpbird eqcomd ) ACUAUKZDZBEDZFZCAGHZABIHZGHZABJKHZI
    HZKHZABJLHZIHZWDWJWLMZWIWLLHZWGMZWDWNWLWILHZWFAGHZACUBHJKHZABUCHZGHZLHZAWFG
    HZWTKHZLHZWGWDWINDZWLNDZWNWPMWCWBWHEDZXEBUDWBXGFONWIPAWHOWAEIUEQRUFZWCWBWKE
    DZXFBUGWBXIFONWLPAWKOWAEIUEQRUFZWIWLUHSWDWLXAWIXCLABUIABUJULWDXDWQXBLHZXBXB
    LHZWGWDWQNDZWTNDZXBNDZXDXKMWDWFNDZANDZXMWDONWFPABOWAEIUEQRZWBXQWCWBAEDXQCAU
    MAUNUOUPZWFATSWDWRNDZWSNDXNWBXTWCWBWRUQURUSDWRUQDXTAUTWRUQURVCWRVAVDUPWDENW
    SVBABEWAEUCVOQRWRWSTSWDXQXPXOXSXRAWFTSZWQWTXBVEVFWDWQXBXBLWDXPXQWQXBMXRXSWF
    AVGSVHWDWGCXBGHZXLWDCNDZXQXPWGYBMYCWDVIVPXSXRCAWFVJVFWDXOYBXLMYAXBVKUOVLVMV
    MWDWGNDZXEXFWMWOVNWDWENDZXPYDWDYCXQYEVIXSCATVQXRWEWFTSXHXJWGWIWLVRVFVSVT $.
    $( [14-Oct-2014] $)

  $( The Y sequence is a Lucas sequence, definable via this second-order
     recurrence with ~ rmy0 and ~ rmy1 .  [JonesMatijasevic] 2.12 #3 ; they use
     this theorem to redefine the X and Y sequences to have domain
     ` ( ZZ X. ZZ ) ` , which simplifies some later theorems.  It may shorten
     the derivation to use this as our initial definition.  Incidentally, the X
     sequence satisfies the exact same recurrence. $)
  rmyluc $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) = ( (
      2 x. ( ( A rmY N ) x. A ) ) - ( A rmY ( N - 1 ) ) ) ) $=
    ( c2 wcel cz c1 caddc co crmy cmin cmul wceq crmx cc zsscn frmy fovcl mulcl
    sseldi syl2anc cuz cfv wa rmyp1 rmym1 oveq12d eluzelre recnd adantr nn0sscn
    cn0 frmx ppncan syl3anc 2cn sylancr peano2zm sylan2 npcan 2times syl eqtr2d
    3eqtrd wb peano2z subcl addcan2 mpbid ) ACUAUBZDZBEDZUCZABFGHZIHZABFJHZIHZG
    HZCABIHZAKHZKHZVPJHZVPGHZLZVNWALZVLVQVSABMHZGHZVSWEJHZGHZVSVSGHZWBVLVNWFVPW
    GGABUDABUEUFVLVSNDZWENDWJWHWILVLVRNDANDZWJVLENVROABEVIEIPQSVJWKVKVJACAUGUHU
    IVRARTZVLUKNWEUJABUKVIEMULQSWLVSWEVSUMUNVLWBVTWIVLVTNDZVPNDZWBVTLVLCNDWJWMU
    OWLCVSRUPZVLENVPOVKVJVOEDVPEDBUQAVOEVIEIPQURSZVTVPUSTVLWJVTWILWLVSUTVAVBVCV
    LVNNDWANDZWNWCWDVDVLENVNOVKVJVMEDVNEDBVEAVMEVIEIPQURSVLWMWNWQWOWPVTVPVFTWPV
    NWAVPVGUNVH $.
    $( [1-Oct-2014] $)

  $( Lucas sequence property of Y with better output ordering. $)
  rmyluc2 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) =
        ( ( ( 2 x. A ) x. ( A rmY N ) ) - ( A rmY ( N - 1 ) ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc co crmy cmul cmin rmyluc wceq frmy zcn syl
    cc fovcl eluzelz adantr mulcom syl2anc oveq2d 2cn a1i mulass syl3anc eqtr4d
    oveq1d eqtrd ) ACDEZFZBGFZHZABIJKLKCABLKZAMKZMKZABINKLKZNKCAMKURMKZVANKABOU
    QUTVBVANUQUTCAURMKZMKZVBUQUSVCCMUQURTFZATFZUSVCPUQURGFVEABGUNGLQUAURRSZUOVF
    UPUOAGFVFCAUBARSUCZURAUDUEUFUQCTFZVFVEVBVDPVIUQUGUHVHVGCAURUIUJUKULUM $.
    $( [16-Oct-2014] $)

  $( "Double-angle formula" for X-values. $)
  rmxdbl $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( 2 x. N ) ) = ( (
      2 x. ( ( A rmX N ) ^ 2 ) ) - 1 ) ) $=
    ( c2 wcel cz cmul co crmx caddc cexp c1 cmin crmy cc wceq 2times syl oveq2d
    cn0 cn cuz cfv wa zcn adantl rmxadd 3anidm23 nn0sscn frmx fovcl sseldi sqcl
    csquarenn cdif rmspecnonsq eldifi nncn 3syl adantr zsscn frmy mulcl syl2anc
    pnncan syl3anc eqcomd rmxynorm oveq12d sqval 3eqtr3rd 3eqtrd ) ACUAUBZDZBED
    ZUCZACBFGZHGABBIGZHGZABHGZVSFGZACJGKLGZABMGZWBFGZFGZIGZCVSCJGZFGZKLGZVOVPVQ
    AHVOBNDZVPVQOVNWIVMBUDUEBPQRVMVNVRWEOABBUFUGVOWFWFIGZWFWAWBCJGZFGZLGZLGZWFW
    LIGZWHWEVOWFNDZWPWLNDZWNWOOVOVSNDZWPVOSNVSUHABSVLEHUIUJUKZVSULQZWTVOWANDZWK
    NDZWQVMXAVNVMWATUMUNDWATDXAAUOWATUMUPWAUQURUSVOWBNDZXBVOENWBUTABEVLEMVAUJUK
    ZWBULQWAWKVBVCWFWFWLVDVEVOWJWGWMKLVOWGWJVOWPWGWJOWTWFPQVFABVGVHVOWFVTWLWDIV
    OWRWFVTOWSVSVIQVOWKWCWAFVOXCWKWCOXDWBVIQRVHVJVK $.
    $( [2-Oct-2014] $)

  $( "Double-angle formula" for Y-values. $)
  rmydbl $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( 2 x. N ) ) = ( (
      2 x. ( A rmX N ) ) x. ( A rmY N ) ) ) $=
    ( c2 cuz cfv wcel cz cmul co crmy caddc crmx cc 2times syl cn0 fovcl sseldi
    wceq syl2anc wa zcn adantl oveq2d rmyadd 3anidm23 2cn a1i nn0sscn frmx frmy
    zsscn mulass syl3anc mulcl mulcom oveq1d 3eqtrrd 3eqtrd ) ACDEZFZBGFZUAZACB
    HIZJIABBKIZJIZABJIZABLIZHIZVHVGHIZKIZCVHHIVGHIZVCVDVEAJVCBMFZVDVESVBVMVABUB
    UCBNOUDVAVBVFVKSABBUEUFVCVLCVJHIZVJVJKIZVKVCCMFZVHMFZVGMFZVLVNSVPVCUGUHVCPM
    VHUIABPUTGLUJQRZVCGMVGULABGUTGJUKQRZCVHVGUMUNVCVJMFZVNVOSVCVQVRWAVSVTVHVGUO
    TVJNOVCVJVIVJKVCVQVRVJVISVSVTVHVGUPTUQURUS $.
    $( [2-Oct-2014] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Ordering and induction lemmas for the integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b x y $.  $d B a b x y $.  $d C a b c d y $.  $d D a x y $.
    $d E a x y $.  $d F b x $.  $d G b x $.  $d H a b c d x y $.
    $d ph a b c d x y $.
    monotuz.1 $e |- ( ( ph /\ y e. H ) -> F < G ) $.
    monotuz.2 $e |- ( ( ph /\ x e. H ) -> C e. RR ) $.
    monotuz.3 $e |- H = ( ZZ>= ` I ) $.
    monotuz.4 $e |- ( x = ( y + 1 ) -> C = G ) $.
    monotuz.5 $e |- ( x = y -> C = F ) $.
    monotuz.6 $e |- ( x = A -> C = D ) $.
    monotuz.7 $e |- ( x = B -> C = E ) $.
    $( A function defined on a set of upper integers which increases at every
       adjacent pair is globally strictly monotonic by induction. $)
    monotuz $p |- ( ( ph /\ ( A e. H /\ B e. H ) ) -> ( A < B <-> D < E ) ) $=
      ( wcel va vb vc vd wa clt wbr csb cv csbeq1 cuz cr cz uzssz zssre eqsstri
      cfv sstri wi ax-17 vex ax17el hbcsb1 hbel weq eleq1 anbi2d csbeq1a eleq1d
      hbim imbi12d chvar simpl adantlrr simplrl sseldi simplrr simpr caddc wceq
      c1 co breq2d imbi2d csbief syl5eqr ovex oveq1 csbeq1d vtoclg w3a 3ad2ant2
      breq12d simp2l cle simp3 zre 3ad2ant1 ltle syl2anc mpd simp11 simp12 eluz
      mpbird simp2r syl6eleq uztrn syl6eleqr peano2uz eleq2i biimpri 3syl lttrd
      wb vtoclf 3exp a2d uzind2 syl3anc ex ltord1 a17d csbiegf breqan12d adantl
      bitrd ) ADKTZEKTZUEZUEDEUFUGBDFUHZBEFUHZUFUGZGHUFUGZAUAUBBUAUIZFUHZBUBUIZ
      FUHZDEKYKYLBYOYQFUJBYODFUJBYOEFUJKLUKUQZULOYSUMULLUNZUOURUPABUIZKTZUEZFUL
      TZUSZAYOKTZUEZYPULTZUSZBUAUUGUUHBUUGBUTZBUCUCYPULBUCYOFUAVAZUCUABVBVCUCUI
      ZULTBUTVDVJBUAVEZUUCUUGUUDUUHUUMUUBUUFAUUAYOKVFVGUUMFYPULBYOFVHVIVKZNVLAU
      UFYQKTZUEUEZYOYQUFUGZYPYRUFUGZUUPUUQUEZUUGUURAUUFUUQUUGUUOUUGUUQVMVNUUSYO
      UMTZYQUMTUUQUUGUURUSZUUSKUMYOKYSUMOYTUPZAUUFUUOUUQVOVPUUSKUMYQUVBAUUFUUOU
      UQVQVPUUPUUQVRUUGYPBUULFUHZUFUGZUSUUGYPBYOWAVSWBZFUHZUFUGZUSZUUGYPBUDUIZF
      UHZUFUGZUSUUGYPBUVIWAVSWBZFUHZUFUGZUSUVAUCUDYOYQUULUVEVTZUVDUVGUUGUVOUVCU
      VFYPUFBUULUVEFUJWCWDUCUDVEZUVDUVKUUGUVPUVCUVJYPUFBUULUVIFUJWCWDUULUVLVTZU
      VDUVNUUGUVQUVCUVMYPUFBUULUVLFUJWCWDUCUBVEZUVDUURUUGUVRUVCYRYPUFBUULYQFUJW
      CWDACUIZKTZUEZIJUFUGZUSZUVHCYOUMCUAVEZUWAUUGUWBUVGUWDUVTUUFAUVSYOKVFVGUWD
      IYPJUVFUFUWDIBUVSFUHZYPBUBUVSFICVAYQITBUTQWEZBUVSYOFUJWFUWDJBUVSWAVSWBZFU
      HZUVFBUBUWGFJUVSWAVSWGYQJTBUTPWEZUWDBUWGUVEFUVSYOWAVSWHWIWFWMVKMWJUUTUVIU
      MTZYOUVIUFUGZWKZUUGUVKUVNUWLUUGUVKUVNUWLUUGUVKWKZYPUVJUVMUUGUWLUUHUVKUUEU
      UIBUAUUGUUHBUUJBUBUBYPULBUBYOFUUKUBUABVBVCYQULTBUTZVDVJUUNNVLWLUWMAUVIKTZ
      UVJULTZUWLAUUFUVKWNZUWMUVIYSKUWMUVIYOUKUQTZYOYSTUVIYSTZUWMUWRYOUVIWOUGZUW
      LUUGUWTUVKUWLUWKUWTUUTUWJUWKWPUWLYOULTZUVIULTZUWKUWTUSUUTUWJUXAUWKYOWQWRU
      WJUUTUXBUWKUVIWQWLYOUVIWSWTXAWRUWMUUTUWJUWRUWTXOUUTUWJUWKUUGUVKXBUUTUWJUW
      KUUGUVKXCYOUVIXDWTXEUWMYOKYSUWLAUUFUVKXFOXGYOUVILXHWTZOXIZUUEAUWOUEZUWPUS
      BUDUXEUWPBUXEBUTBUBUBUVJULBUBUVIFUDVAUBUDBVBVCUWNVDVJBUDVEZUUCUXEUUDUWPUX
      FUUBUWOAUUAUVIKVFVGUXFFUVJULBUVIFVHVIVKNVLWTUWMAUVLKTZUVMULTZUWQUWMUWSUVL
      YSTZUXGUXCLUVIXJUXGUXIKYSUVLOXKXLXMUUEAUXGUEZUXHUSBUVLUXJUXHBUXJBUTBUBUBU
      VMULBUBUVLFUVIWAVSWGZYQUVLTBUTVCUWNVDVJUXKUUAUVLVTZUUCUXJUUDUXHUXLUUBUXGA
      UUAUVLKVFVGUXLFUVMULBUVLFVHVIVKNXPWTUWLUUGUVKWPUWMAUWOUVJUVMUFUGZUWQUXDUW
      CUXEUXMUSZCUDUXNCUTCUDVEZUWAUXEUWBUXMUXOUVTUWOAUVSUVIKVFVGUXOIUVJJUVMUFUX
      OIUWEUVJUWFBUVSUVIFUJWFUXOJUWHUVMUWIUXOBUWGUVLFUVSUVIWAVSWHWIWFWMVKMVLWTX
      NXQXRXSXTXAYAYBYJYMYNXOAYHYIYKGYLHUFBUADFGKYHYOGTBYCRYDBUAEFHKYIYOHTBYCSY
      DYEYFYG $.
      $( [24-Sep-2014] $)
  $}

  ${
    $d ph a b x y $.  $d A a b x y $.  $d B a b x y $.  $d F a b x y $.
    monotoddzzfi.1 $e |- ( ( ph /\ x e. ZZ ) -> ( F ` x ) e. RR ) $.
    monotoddzzfi.2 $e |- ( ( ph /\ x e. ZZ ) -> ( F ` -u x ) = -u ( F ` x ) )
        $.
    monotoddzzfi.3 $e |- ( ( ph /\ x e. NN0 /\ y e. NN0 ) -> ( x < y -> ( F ` x
        ) < ( F ` y ) ) ) $.
    $( A function which is odd and monotonic on ` NN0 ` is monotonic on
       ` ZZ ` .  This proof is far too long. $)
    monotoddzzfi $p |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> ( F ` A )
        < ( F ` B ) ) ) $=
      ( cz wcel clt wbr wa cr wi imbi12d cn0 cc0 cle va vb wb fveq2 zssre eleq1
      cfv cv weq anbi2d eleq1d chvarv cn wo elznn simprbi anim12i adantl simpll
      nnnn0 ad2antrl ad2antll w3a vex simpl eqidd eleq12d simpr 3anbi23d breq12
      cneg breqan12d vtocl2 syl3anc adantrr adantr 0re a1i adantrl elnn0 biimpi
      ex wceq fveq2i 0z elexi negeq fveq2d negeqd eqeq12d vtocl mpan2 eqtr3d cc
      neg0 recnd eqneg syl mpbid ad2antrr nngt0 simplll simplrl fveq12d breq12d
      0nn0 negex mpd eqbrtrrd znegcl syl2anc ltle breqtrrd breq2d mpbird jaodan
      nn0ge0i mpdan breqtrd le0neg1 lelttrd a1d wn simp3 c1 zre ad2antlr nn0ge0
      1re nnre 1nn0 letrd nnge1 lenlt 3adant3 pm2.24 sylc 3exp 3ancomb ltneg
      sylbi 3expb adantlr sylibd 3imtr4d ccased ltord1 3impb ) ADJKEJKDELMDFUGZ
      EFUGZLMUCAUAUBUAUHZFUGZUBUHZFUGZDEJUUIUUJUUKUUMFUDUUKDFUDUUKEFUDUEABUHZJK
      ZNZUUOFUGZOKZPZAUUKJKZNZUULOKZPBUABUAUIZUUQUVBUUSUVCUVDUUPUVAAUUOUUKJUFUJ
      ZUVDUURUULOUUOUUKFUDZUKQGULZAUVAUUMJKZNZNZUUKUMKZUUKVKZRKZUNZUUMUMKZUUMVK
      ZRKZUNZNZUUKUUMLMZUULUUNLMZPZUVIUVSAUVAUVNUVHUVRUVAUUKOKZUVNUUKUOUPUVHUUM
      OKZUVRUUMUOUPUQURUVJUVKUVOUVMUVQUWBUVJUVKUVONZUWBUVJUWENAUUKRKZUUMRKZUWBA
      UVIUWEUSUVKUWFUVJUVOUUKUTVAUVOUWGUVJUVKUUMUTZVBAUUORKZCUHZRKZVCZUUOUWJLMZ
      UURUWJFUGZLMZPZPZAUWFUWGVCZUWBPBCUUKUUMUAVDUBVDZUVDCUBUIZNZUWLUWRUWPUWBUX
      AUWIUWFUWKUWGAUXAUUOUUKRRUVDUWTVEUXARVFZVGUXAUWJUUMRRUVDUWTVHUXBVGVIUXAUW
      MUVTUWOUWAUUOUUKUWJUUMLVJUVDUWTUURUULUWNUUNLUVFUWJUUMFUDZVLQQIVMVNWBUVJUV
      MUVONZUWBUVJUXDNZUWAUVTUXEUULSUUNUVJUVCUXDAUVAUVCUVHUVGVOZVPZSOKZUXEVQVRZ
      UVJUUNOKZUXDAUVHUXJUVAUUTAUVHNZUXJPBUBBUBUIZUUQUXKUUSUXJUXLUUPUVHAUUOUUMJ
      UFUJZUXLUURUUNOUUOUUMFUDZUKQGULVSZVPUXEUULSTMZSUULVKZTMZUXESUVLFUGZUXQTUX
      EUVLUMKZUVLSWCZUNZSUXSTMZUVMUYBUVJUVOUVMUYBUVLVTWAVAUXEUXTUYCUYAUXEUXTNZS
      UXSLMZUYCUYDSFUGZSUXSLUVJUYFSWCZUXDUXTAUYGUVIAUYFUYFVKZWCZUYGASVKZFUGZUYF
      UYHUYKUYFWCAUYJSFWOWDVRASJKZUYKUYHWCZWEUUQUUOVKZFUGZUURVKZWCZPZAUYLNZUYMP
      BSSOVQWFZUUOSWCZUUQUYSUYQUYMVUAUUPUYLAUUOSJUFUJZVUAUYOUYKUYPUYHVUAUYNUYJF
      UUOSWGWHVUAUURUYFUUOSFUDZWIWJQHWKWLWMAUYFWNKUYIUYGUCAUYFAUYLUYFOKZWEUUTUY
      SVUDPBSUYTVUAUUQUYSUUSVUDVUBVUAUURUYFOVUCUKQGWKWLWPUYFWQWRWSVPZWTUYDSUVLL
      MZUYFUXSLMZUXTVUFUXEUVLXAURUYDASRKZUVMVUFVUGPZAUVIUXDUXTXBVUHUYDXFVRUVJUV
      MUVOUXTXCUWQAVUHUVMVCZVUIPBCSUVLUYTUUKXGZVUAUWJUVLWCZNZUWLVUJUWPVUIVUMUWI
      VUHUWKUVMAVUMUUOSRRVUAVULVEZVUMRVFZVGVUMUWJUVLRRVUAVULVHZVUOVGVIVUMUWMVUF
      UWOVUGUUOSUWJUVLLVJVUMUURUYFUWNUXSLVUMUUOSFFVUMFVFZVUNXDVUMUWJUVLFFVUQVUP
      XDXEQQIVMVNXHXIUYDUXHUXSOKZUYEUYCPUXEUXHUXTUXIVPUVJVURUXDUXTUVJAUVLJKZVUR
      AUVIVEUVAVUSAUVHUUKXJVAUUTAVUSNZVURPBUVLVUKUUOUVLWCZUUQVUTUUSVURVVAUUPVUS
      AUUOUVLJUFUJVVAUURUXSOUUOUVLFUDUKQGWKXKWTSUXSXLXKXHUXEUYANZUYCSUYFTMZVVBS
      SUYFTSSTMVVBSXFXQVRUVJUYGUXDUYAVUEWTXMUYAUYCVVCUCUXEUYAUXSUYFSTUVLSFUDXNU
      RXOXPXRUVJUXSUXQWCZUXDAUVAVVDUVHUYRUVBVVDPBUAUVDUUQUVBUYQVVDUVEUVDUYOUXSU
      YPUXQUVDUYNUVLFFUVDFVFUUOUUKWGXDUVDUURUULUVFWIWJQHULVOZVPXSUXEUVCUXPUXRUC
      UXGUULXTWRXOUXEUYFSUUNLUVJUYGUXDVUEVPUXESUUMLMZUYFUUNLMZUVOVVFUVJUVMUUMXA
      VBUXEAVUHUWGVVFVVGPZAUVIUXDUSVUHUXEXFVRUVOUWGUVJUVMUWHVBUWQAVUHUWGVCZVVHP
      BCSUUMUYTUWSVUAUWTNZUWLVVIUWPVVHVVJUWIVUHUWKUWGAVVJUUOSRRVUAUWTVEVVJRVFZV
      GVVJUWJUUMRRVUAUWTVHVVKVGVIVVJUWMVVFUWOVVGUUOSUWJUUMLVJVUAUWTUURUYFUWNUUN
      LVUCUXCVLQQIVMVNXHXIYAYBWBUVJUVKUVQNZUVTUWAUVJVVLUVTVCUVTUVTYCZUWAUVJVVLU
      VTYDUVJVVLVVMUVTUVJVVLNZUUMUUKTMZVVMVVNUUMYEUUKUVIUWDAVVLUVHUWDUVAUUMYFUR
      ZYGZYEOKVVNYIVRZUVKUWCUVJUVQUUKYJVAZVVNUUMSYEVVQUXHVVNVQVRVVRVVNUUMSTMZSU
      VPTMZUVQVWAUVJUVKUVPYHVBVVNUWDVVTVWAUCVVQUUMXTWRXOSYETMVVNYEYKXQVRYLUVKYE
      UUKTMUVJUVQUUKYMVAYLVVNUWDUWCVVOVVMUCVVQVVSUUMUUKYNXKWSYOUVTUWAYPYQYRUVJU
      VMUVQNZUWBUVJVWBNZUVPUVLLMZUUNVKZUXQLMZUVTUWAVWCVWDUVPFUGZUXSLMZVWFAVWBVW
      DVWHPZUVIAUVMUVQVWIAUVMUVQVCAUVQUVMVCZVWIAUVMUVQYSUWQVWJVWIPBCUVPUVLUUMXG
      VUKUUOUVPWCZVULNZUWLVWJUWPVWIVWLUWIUVQUWKUVMAVWLUUOUVPRRVWKVULVEVWLRVFZVG
      VWLUWJUVLRRVWKVULVHVWMVGVIVWLUWMVWDUWOVWHUUOUVPUWJUVLLVJVWKVULUURVWGUWNUX
      SLUUOUVPFUDUWJUVLFUDVLQQIVMUUAUUBUUCVWCVWGVWEUXSUXQLUVJVWGVWEWCZVWBAUVHVW
      NUVAUYRUXKVWNPBUBUXLUUQUXKUYQVWNUXMUXLUYOVWGUYPVWEUXLUYNUVPFFUXLFVFUUOUUM
      WGXDUXLUURUUNUXNWIWJQHULVSVPUVJVVDVWBVVEVPXEUUDVWCUWCUWDUVTVWDUCUVJUWCVWB
      UVAUWCAUVHUUKYFVAVPUVIUWDAVWBVVPYGUUKUUMYTXKVWCUVCUXJUWAVWFUCUVJUVCVWBUXF
      VPUVJUXJVWBUXOVPUULUUNYTXKUUEWBUUFXHUUGUUH $.
      $( [25-Sep-2014] $)
  $}

  ${
    $d ph a b x y $.  $d A a b x y $.  $d B a b x y $.  $d E a b y $.
    $d C a b x y $.  $d D a b x y $.  $d F a b x $.  $d G a b x $.
    monotoddzz.1 $e |- ( ( ph /\ x e. NN0 /\ y e. NN0 ) -> ( x < y -> E < F ) )
        $.
    monotoddzz.2 $e |- ( ( ph /\ x e. ZZ ) -> E e. RR ) $.
    monotoddzz.3 $e |- ( ( ph /\ y e. ZZ ) -> G = -u F ) $.
    monotoddzz.4 $e |- ( x = A -> E = C ) $.
    monotoddzz.5 $e |- ( x = B -> E = D ) $.
    monotoddzz.6 $e |- ( x = y -> E = F ) $.
    monotoddzz.7 $e |- ( x = -u y -> E = G ) $.
    $( A function (given implicitly) which is odd and monotonic on ` NN0 ` is
       monotonic on ` ZZ ` .  This proof is far too long. $)
    monotoddzz $p |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> C < D ) ) $=
      ( cz wcel cr va vb w3a clt wbr cmpt cfv cv wa wi ax-17 hbmpt1 ax17el hbfv
      hbel hbim weq eleq1 anbi2d fveq2 eleq1d imbi12d wceq simpr fvmpt2 syl2anc
      eqid eqeltrd chvar negeq fveq2d negeqd eqeq12d znegcl adantl negex sylan2
      cneg vtocl fvmptg chvarv 3eqtr4d hbbr 3anbi2d breq1 breq1d 3anbi3d breq2d
      breq2 nn0z 3adant3 hbeq 3adant2 breq12d sylibrd monotoddzzfi simp2 vtoclg
      cn0 anabsi7 simp3 bitrd ) ADRSZERSZUCZDEUDUEDBRHUFZUGZEXFUGZUDUEFGUDUEAUA
      UBDEXFABUHZRSZUIZXIXFUGZTSZUJAUAUHZRSZUIZXNXFUGZTSZUJBUAXPXRBXPBUKBUBUBXQ
      TBUBXNXFBUBRHULUBUABUMUNUBUHZTSBUKUOUPBUAUQZXKXPXMXRXTXJXOAXIXNRURUSXTXLX
      QTXIXNXFUTZVAVBXKXLHTXKXJHTSZXLHVCZAXJVDLBRHTXFXFVGZVEVFZLVHVIACUHZRSZUIZ
      YFVRZXFUGZYFXFUGZVRZVCZUJXPXNVRZXFUGZXQVRZVCZUJCUACUAUQZYHXPYMYQYRYGXOAYF
      XNRURUSYRYJYOYLYPYRYIYNXFYFXNVJVKYRYKXQYFXNXFUTVLVMVBYHJIVRYJYLMYHYIRSZJT
      SZYJJVCYGYSAYFVNZVOYGAYSYTUUAXKYBUJZAYSUIZYTUJBYIYFVPXIYIVCZXKUUCYBYTUUDX
      JYSAXIYIRURUSUUDHJTQVAVBLVSVQBYIHJRTXFQYDVTVFYHYKIYHYGITSZYKIVCZAYGVDUUBY
      HUUEUJBCBCUQZXKYHYBUUEUUGXJYGAXIYFRURUSUUGHITPVAVBLWABYFHIRTXFPYDVTVFVLWB
      WAAXIWSSZXSWSSZUCZXIXSUDUEZXLXSXFUGZUDUEZUJZUJZAXNWSSZUUIUCZXNXSUDUEZXQUU
      LUDUEZUJZUJBUAUUQUUTBUUQBUKUURUUSBUURBUKBCXQUULUDBCXNXFBCRHULZCUABUMUNYFU
      DSBUKBCXSXFUVACUBBUMUNWCUPUPXTUUJUUQUUNUUTXTUUHUUPAUUIXIXNWSURWDXTUUKUURU
      UMUUSXIXNXSUDWEXTXLXQUULUDYAWFVBVBAUUHYFWSSZUCZXIYFUDUEZXLYKUDUEZUJZUJUUO
      CUBCUBUQZUVCUUJUVFUUNUVGUVBUUIAUUHYFXSWSURWGUVGUVDUUKUVEUUMYFXSXIUDWIUVGY
      KUULXLUDYFXSXFUTWHVBVBUVCUVDHIUDUEUVEKUVCXLHYKIUDAUUHYCUVBUUHAXJYCXIWJYEV
      QZWKAUVBUUFUUHAUUHUIZYCUJAUVBUIZUUFUJBCUVJUUFBUVJBUKBUAUAYKIBUAYFXFBUARHU
      LUACBUMUNXNISBUKWLUPUUGUVIUVJYCUUFUUGUUHUVBAXIYFWSURUSUUGXLYKHIXIYFXFUTPV
      MVBUVHVIWMWNWOWAVIWPXEXGFXHGUDXEXCFTSZXGFVCAXCXDWQAXCUVKXDAXCUVKUUBAXCUIZ
      UVKUJBDRXIDVCZXKUVLYBUVKUVMXJXCAXIDRURUSUVMHFTNVAVBLWRWTWKBDHFRTXFNYDVTVF
      XEXDGTSZXHGVCAXCXDXAAXDUVNXCAXDUVNUUBAXDUIZUVNUJBERXIEVCZXKUVOYBUVNUVPXJX
      DAXIERURUSUVPHGTOVAVBLWRWTWMBEHGRTXFOYDVTVFWNXB $.
      $( [25-Sep-2014] $)

    $( The impression which I am slowly getting is that the major difference between ` ( F `` y ) ` and ` [_ y / x ]_ F ` is that the latter can have proper classes in its range.  Shifting between the two requires proofs of setness.  It is possible the former two theorems could be substantially shortened using a class substitution step instead of a function step $)
  $}

  $( TODO: abstract concept of a symmetric set of reals, and use that instead of ZZ here and in monotoddzz $)
  ${
    $d B a b x $.  $d C a b x $.  $d D a b x y $.  $d E a b x $.  $d F a b x $.
    $d A a b y $.  $d ph a b x y $.
    oddcomabszz.1 $e |- ( ( ph /\ x e. ZZ ) -> A e. RR ) $.
    oddcomabszz.2 $e |- ( ( ph /\ x e. ZZ /\ 0 <_ x ) -> 0 <_ A ) $.
    oddcomabszz.3 $e |- ( ( ph /\ y e. ZZ ) -> C = -u B ) $.
    oddcomabszz.4 $e |- ( x = y -> A = B ) $.
    oddcomabszz.5 $e |- ( x = -u y -> A = C ) $.
    oddcomabszz.6 $e |- ( x = D -> A = E ) $.
    oddcomabszz.7 $e |- ( x = ( abs ` D ) -> A = F ) $.
    $( An odd function which takes nonnegative values on nonnegative arguments
       commutes with ` abs ` . $)
    oddcomabszz $p |- ( ( ph /\ D e. ZZ ) -> ( abs ` E ) = F ) $=
      ( va wcel cc0 cle vb cz wa csb cabs wceq cv wi eleq1 anbi2d csbeq1 fveq2d
      cfv fveq2 csbeq1d eqeq12d imbi12d wbr wo cr 0re zre letric sylancr adantl
      ax-17 vex ax17el hbcsb1 hbel hbim weq csbeq1a eleq1d chvar w3a hbbr breq2
      adantr 3anbi23d breq2d 3expa absid syl2anc ad2antlr sylancom eqtr4d negex
      csbief negeq syl5eqr negeqd absnid znegcl vtoclf 3expia sylan2 wb le0neg1
      cneg sylibd syl 3imtr4d 3eqtr4rd jaodan mpdan vtoclg anabsi7 a17d csbiegf
      imp fvex a1i 3eqtr3d ) AGUBRZUCZBGDUDZUEUMZBGUEUMZDUDZHUEUMZIAXOXRXTUFZAQ
      UGZUBRZUCZBYCDUDZUEUMZBYCUEUMZDUDZUFZUHXPYBUHQGUBYCGUFZYEXPYJYBYKYDXOAYCG
      UBUIUJYKYGXRYIXTYKYFXQUEBYCGDUKULYKBYHXSDYCGUEUNUOUPUQYESYCTURZYCSTURZUSZ
      YJYDYNAYDSUTRYCUTRZYNVAYCVBZSYCVCVDVEYEYLYJYMYEYLUCZYGYFYIYQYFUTRZSYFTURZ
      YGYFUFYEYRYLABUGZUBRZUCZDUTRZUHYEYRUHBQYEYRBYEBVFBUAQYFUTBUAYCDQVGUAQBVHV
      IZYOBVFVJVKBQVLZUUBYEUUCYRUUEUUAYDAYTYCUBUIZUJUUEDYFUTBYCDVMZVNUQJVOZVSAY
      DYLYSAUUASYTTURZVPZSDTURZUHZAYDYLVPZYSUHBQUUMYSBUUMBVFBUASYFTUAUGZSRBVFZU
      UNTRBVFZUUDVQVKUUEUUJUUMUUKYSUUEUUAYDUUIYLAUUFYTYCSTVRVTUUEDYFSTUUGWAUQKV
      OWBYFWCWDYQBYHYCDYEYLYOYHYCUFYDYOAYLYPWEYCWCWFUOWGYEYMUCZBYCWTZDUDZYFWTZY
      IYGYEUUSUUTUFZYMACUGZUBRZUCZFEWTZUFZUHYEUVAUHZCQUVGCVFCQVLZUVDYEUVFUVAUVH
      UVCYDAUVBYCUBUIUJUVHFUUSUVEUUTUVHFBUVBWTZDUDUUSBQUVIDFUVBWHYCFRBVFNWIUVHB
      UVIUURDUVBYCWJUOWKUVHEYFUVHEBUVBDUDYFBQUVBDECVGYCERBVFMWIBUVBYCDUKWKWLUPU
      QLVOZVSUUQBYHUURDYEYMYOYHUURUFYDYOAYMYPWEYCWMWFUOUUQYRYFSTURZYGUUTUFYEYRY
      MUUHVSYEYMUVKYESUURTURZSUUTTURZYMUVKYEUVLSUUSTURZUVMYDAUURUBRZUVLUVNUHYCW
      NAUVOUVLUVNUULAUVOUVLVPZUVNUHBUURUVPUVNBUVPBVFBUASUUSTUUOUUPBUAUURDYCWHZU
      UNUURRBVFVIVQVKUVQYTUURUFZUUJUVPUUKUVNUVRUUAUVOUUIUVLAYTUURUBUIYTUURSTVRV
      TUVRDUUSSTBUURDVMWAUQKWOWPWQYEUUSUUTSTUVJWAXAYEYOYMUVLWRYDYOAYPVEYCWSXBYE
      YRUVKUVMWRUUHYFWSXBXCXKYFWMWDXDXEXFXGXHXOXRYAUFAXOXQHUEBQGDHUBXOYCHRBXIOX
      JULVEXTIUFXPBQXSDIGUEXLYCIRBVFPWIXMXN $.
      $( [26-Sep-2014] $)
  $}

  ${
    $d a b c x y $.  $d a b c x A $.  $d ps a b c x $.  $d ch a b c x $.
    $d th a b c x $.  $d ta a b c x $.  $d et a b c x $.  $d rh a b c x $.
    $d ph a b c y $.
    2nn0ind.1 $e |- ps $.
    2nn0ind.2 $e |- ch $.
    2nn0ind.3 $e |- ( y e. NN -> ( ( th /\ ta ) -> et ) ) $.
    2nn0ind.4 $e |- ( x = 0 -> ( ph <-> ps ) ) $.
    2nn0ind.5 $e |- ( x = 1 -> ( ph <-> ch ) ) $.
    2nn0ind.6 $e |- ( x = ( y - 1 ) -> ( ph <-> th ) ) $.
    2nn0ind.7 $e |- ( x = y -> ( ph <-> ta ) ) $.
    2nn0ind.8 $e |- ( x = ( y + 1 ) -> ( ph <-> et ) ) $.
    2nn0ind.9 $e |- ( x = A -> ( ph <-> rh ) ) $.
    $( Induction on natural numbers with two base cases, for use with
       Lucas-type sequences. $)
    2nn0ind $p |- ( A e. NN0 -> rh ) $=
      ( c1 va cn0 wcel wsbc caddc co cmin wa cn nn0p1nn cv wceq wb oveq1 dfsbcq
      wsb syl anbi12d weq ovex cc0 ax-1cn subidi eqeq2i sylbi sbcie mpbir elexi
      cc pm3.2i simprr nncn pncan sylancl adantr mpbird vex anbi12i 3imtr4g imp
      jca ex nnind nn0cn biimpa adantrr mpdan sbcieg mpbid ) JUBUCZAHJUDZGWJAHJ
      TUEUFZTUGUFZUDZAHWLUDZUHZWKWJWLUIUCWPJUJAHUAUKZTUGUFZUDZAHUAUPZUHAHTTUGUF
      ZUDZAHTUDZUHAHIUKZTUGUFZUDZAHIUPZUHZAHXDTUEUFZTUGUFZUDZAHXIUDZUHZWPUAIWLW
      QTULZWSXBWTXCXNWRXAULWSXBUMWQTTUGUNAHWRXAUOUQAHWQTUOURUAIUSZWSXFWTXGXOWRX
      EULWSXFUMWQXDTUGUNAHWRXEUOUQAHWQXDUOURWQXIULZWSXKWTXLXPWRXJULWSXKUMWQXITU
      GUNAHWRXJUOUQAHWQXIUOURWQWLULZWSWNWTWOXQWRWMULWSWNUMWQWLTUGUNAHWRWMUOUQAH
      WQWLUOURXBXCXBBKABHXATTUGUTHUKZXAULXRVAULABUMXAVAXRTVBVCVDNVEVFVGXCCLACHT
      TVIVBVHOVFVGVJXDUIUCZXHXMXSXHUHZXKXLXTXKXGXSXFXGVKXTXJXDULZXKXGUMXSYAXHXS
      XDVIUCTVIUCZYAXDVLVBXDTVMVNVOAHXJXDUOUQVPXSXHXLXSDEUHFXHXLMXFDXGEADHXEXDT
      UGUTPVFAEHXDIVQQVFVRAFHXIXDTUEUTRVFVSVTWAWBWCUQWJWNWKWOWJWNWKWJWMJULZWNWK
      UMWJJVIUCYBYCJWDVBJTVMVNAHWMJUOUQWEWFWGAGHJUBSWHWI $.
      $( [1-Oct-2014] $)
  $}

  ${
    $d ph a b y $.  $d A a b x y $.  $d ps a b x $.  $d ch a b x $.
    $d th a b x $.  $d ta a b x $.
    zindbi.1 $e |- ( y e. ZZ -> ( ps <-> ch ) ) $.
    zindbi.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    zindbi.3 $e |- ( x = ( y + 1 ) -> ( ph <-> ch ) ) $.
    zindbi.4 $e |- ( x = 0 -> ( ph <-> th ) ) $.
    zindbi.5 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Inductively transfer a property to the integers if it holds for zero and
       passes between adjacent integers in either direction. $)
    zindbi $p |- ( A e. ZZ -> ( th <-> ta ) ) $=
      ( vb cz wcel cc0 cle wb dfsbcq va wbr wo cr 0re zre letric sylancr 0z w3a
      wsbc wi cv wceq eleq1 breq1 3anbi13d bibi1d imbi12d breq2 3anbi23d bibi2d
      wsb c1 caddc co weq biidd vex sbcie syl5bbr ovex bibi12d vtoclga 3ad2ant2
      oveq1 biimpd uzind vtocl2g 3adant3 pm2.43i mp3an1 wa mp3an2 bicomd jaodan
      syl mpdan elexi a1i sbcieg 3bitr3d ) HOPZAFQUKZAFHUKZDEWMQHRUBZHQRUBZUCZW
      NWOSZWMQUDPHUDPWRUEHUFQHUGUHWMWPWSWQQOPZWMWPWSUIWTWMWPUJZWSWTWMXAWSULZWPG
      UMZOPZNUMZOPZXCXERUBZUJZAFGVCZAFNVCZSZULZWTXFQXERUBZUJZWNXJSZULXBGNQHOOXC
      QUNZXHXNXKXOXPXDWTXGXMXFXCQOUOXCQXERUPUQXPXIWNXJAFXCQTURUSXEHUNZXNXAXOWSX
      QXFWMXMWPWTXEHOUOXEHQRUTVAXQXJWOWNAFXEHTVBUSXIAFUAVCZSXIXISXKXIAFXEVDVEVF
      ZUKZSZXKUANXCXEUAGVGXRXIXIAFUAUMZXCTVBUANVGXRXJXIAFYBXETVBZYBXSUNXRXTXIAF
      YBXSTVBYCXDXIVHXHXKYAXHXJXTXIXFXDXJXTSZXGBCSYDGXEOGNVGZBXJCXTBXIYEXJABFXC
      GVIJVJAFXCXETVKCAFXCVDVEVFZUKZYEXTACFYFXCVDVEVLKVJYEYFXSUNYGXTSXCXEVDVEVP
      AFYFXSTWGVKVMIVNVOVBVQVRZVSVTWAWBWMWQWCWOWNWMWTWQWOWNSZUIWMWTWQUJZYIWMWTY
      JYIULZWQXLWMXFHXERUBZUJZWOXJSZULYKGNHQOOXCHUNZXHYMXKYNYOXDWMXGYLXFXCHOUOX
      CHXERUPUQYOXIWOXJAFXCHTURUSXEQUNZYMYJYNYIYPXFWTYLWQWMXEQOUOXEQHRUTVAYPXJW
      NWOAFXEQTVBUSYHVSVTWAWDWEWFWHWNDSWMADFQQOUIWILVJWJAEFHOMWKWL $.
      $( [1-Oct-2014] $)
  $}

  ${
    $d A a b $.  $d B a b $.  $d N a b $.

    $( Mantissa ordering relationship for exponentiation. $)
    expmordi $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ A < B ) /\
        N e. NN ) -> ( A ^ N ) < ( B ^ N ) ) $=
      ( va vb cr wcel wa cc0 wbr clt cexp co wi c1 oveq2 breq12d imbi2d syl2anc
      wceq cle cn cv caddc weq cc wb recn exp1 breqan12d syl2an biimpar adantrl
      w3a cn0 simp2ll nnnn0 3ad2ant1 reexpcl simp2lr jca simp2rl expge0 syl3anc
      cmul simp3 simp2l simp2r ltmul12a syl22anc recnd expp1 3brtr4d 3exp nnind
      a2d impcom 3impa ) AFGZBFGZHZIAUAJZABKJZHZCUBGZACLMZBCLMZKJZWEWAWDHZWHWIA
      DUCZLMZBWJLMZKJZNWIAOLMZBOLMZKJZNWIAEUCZLMZBWQLMZKJZNWIAWQOUDMZLMZBXALMZK
      JZNWIWHNDECWJOTZWMWPWIXEWKWNWLWOKWJOALPWJOBLPQRDEUEZWMWTWIXFWKWRWLWSKWJWQ
      ALPWJWQBLPQRWJXATZWMXDWIXGWKXBWLXCKWJXAALPWJXABLPQRWJCTZWMWHWIXHWKWFWLWGK
      WJCALPWJCBLPQRWAWCWPWBWAWPWCVSAUFGZBUFGZWPWCUGVTAUHBUHXIXJWNAWOBKAUIBUIUJ
      UKULUMWQUBGZWIWTXDXKWIWTXDXKWIWTUNZWRAVEMZWSBVEMZXBXCKXLWRFGZWSFGZHIWRUAJ
      ZWTHWAWDXMXNKJXLXOXPXLVSWQUOGZXOVSVTWDXKWTUPZXKWIXRWTWQUQURZAWQUSSXLVTXRX
      PVSVTWDXKWTUTZXTBWQUSSVAXLXQWTXLVSXRWBXQXSXTWBWCWAXKWTVBAWQVCVDXKWIWTVFVA
      XKWAWDWTVGXKWAWDWTVHWRWSABVIVJXLXIXRXBXMTXLAXSVKXTAWQVLSXLXJXRXCXNTXLBYAV
      KXTBWQVLSVMVNVPVOVQVR $.
      $( [16-Oct-2014] $)

    $( Mantissa ordering relationship for exponentiation of positive reals. $)
    rpexpmord $p |- ( ( N e. NN /\ A e. RR+ /\ B e. RR+ ) -> ( A < B <->
        ( A ^ N ) < ( B ^ N ) ) ) $=
      ( va vb cn wcel crp clt wbr cexp co wb cv oveq1 rpssre cr rpre wa syl cn0
      nnnn0 reexpcl syl2anr cc0 cle simplrl simplrr rpge0 simpr simpll expmordi
      syl221anc ex ltord1 3impb ) CFGZAHGBHGABIJACKLZBCKLZIJMUQDEDNZCKLZENZCKLZ
      ABHURUSUTVBCKOUTACKOUTBCKOPUTHGZUTQGZCUAGVAQGUQUTRZCUBUTCUCUDUQVDVBHGZSZS
      ZUTVBIJZVAVCIJZVIVJSZVEVBQGZUEUTUFJZVJUQVKVLVDVEUQVDVGVJUGZVFTVLVGVMUQVDV
      GVJUHVBRTVLVDVNVOUTUITVIVJUJUQVHVJUKUTVBCULUMUNUOUP $.
      $( [16-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    X and Y sequences 2: Order properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b A $.  $d a b N $.
    $( For all nonnegative indices, X is positive and Y is nonnegative. $)
    rmxypos $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( 0 < ( A rmX N ) /\ 0
        <_ ( A rmY N ) ) ) $=
      ( cn0 wcel c2 cc0 crmx co clt wbr crmy wa wi wceq oveq2 breq2d cr syl2anc
      cle syl va vb cuz cfv cv c1 caddc anbi12d imbi2d lt01 rmx0 syl5breqr 0nn0
      weq nn0ge0i rmy0 jca w3a cmul cexp cmin cz simp2 nn0z 3ad2ant1 frmx fovcl
      nn0re eluzelre 3ad2ant2 remulcl crp rmspecpos rpre frmy zre simp3l cn wss
      uznnssnn ax-mp sseli nngt0 mulgt0 syl22anc rpge0 simp3r addgtge0 breqtrrd
      2nn mulge0 rmxp1 2nn0 eluznn0 mpan nn0ge0 addge0 rmyp1 3exp nn0ind impcom
      a2d ) BCDAEUCUDZDZFABGHZIJZFABKHZSJZLZXDFAUAUEZGHZIJZFAXJKHZSJZLZMXDFAFGH
      ZIJZFAFKHZSJZLZMXDFAUBUEZGHZIJZFAYAKHZSJZLZMXDFAYAUFUGHZGHZIJZFAYGKHZSJZL
      ZMXDXIMUAUBBXJFNZXOXTXDYMXLXQXNXSYMXKXPFIXJFAGOPYMXMXRFSXJFAKOPUHUIUAUBUN
      ZXOYFXDYNXLYCXNYEYNXKYBFIXJYAAGOPYNXMYDFSXJYAAKOPUHUIXJYGNZXOYLXDYOXLYIXN
      YKYOXKYHFIXJYGAGOPYOXMYJFSXJYGAKOPUHUIXJBNZXOXIXDYPXLXFXNXHYPXKXEFIXJBAGO
      PYPXMXGFSXJBAKOPUHUIXDXQXSXDFUFXPIUJAUKULXDFFXRSFUMUOAUPULUQYACDZXDYFYLYQ
      XDYFYLYQXDYFURZYIYKYRFYBAUSHZAEUTHUFVAHZYDUSHZUGHZYHIYRYSQDZUUAQDZFYSIJZF
      UUASJZFUUBIJYRYBQDZAQDZUUCYRYBCDZUUGYRXDYAVBDZUUIYQXDYFVCZYQXDUUJYFYAVDVE
      ZAYACXCVBGVFVGRZYBVHTZXDYQUUHYFEAVIVJZYBAVKRYRYTQDZYDQDZUUDXDYQUUPYFXDYTV
      LDZUUPAVMZYTVNTVJZYRYDVBDZUUQYRXDUUJUVAUUKUULAYAVBXCVBKVOVGRYDVPTZYTYDVKR
      YRUUGYCUUHFAIJZUUEUUNYQXDYCYEVQUUOXDYQUVCYFXDAVRDUVCXCVRAEVRDXCVRVSWJEVTW
      AWBAWCTVJYBAWDWEYRUUPFYTSJZUUQYEUUFUUTXDYQUVDYFXDUURUVDUUSYTWFTVJUVBYQXDY
      CYEWGZYTYDWKWEYSUUAWHWEYRXDUUJYHUUBNUUKUULAYAWLRWIYRFYDAUSHZYBUGHZYJSYRUV
      FQDZUUGFUVFSJZFYBSJZFUVGSJYRUUQUUHUVHUVBUUOYDAVKRUUNYRUUQYEUUHFASJZUVIUVB
      UVEUUOXDYQUVKYFXDACDZUVKECDXDUVLWMAEWNWOAWPTVJYDAWKWEYRUUIUVJUUMYBWPTUVFY
      BWQWEYRXDUUJYJUVGNUUKUULAYAWRRWIUQWSXBWTXA $.
      $( [24-Sep-2014] $)
  $}


  ${
    $d N a b $.  $d M a b $.  $d A a b $.
    $( The Y-sequence is strictly monotonic on ` NN0 ` .  Strengthened by
       ~ ltrmy . $)
    ltrmynn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N
        <-> ( A rmY M ) < ( A rmY N ) ) ) $=
      ( c2 wcel cn0 clt wbr crmy co cc0 cz cr fovcl sylan2 sseldi syl2anc oveq2
      cle cn va vb cuz cfv wb cv c1 caddc wa cmul crmx zssre nn0z frmy eluzelre
      adantr remulcl nn0ssre frmx readdcl rmxypos simprd wss 2nn uznnssnn ax-mp
      sseli nnge1 syl lemulge11 syl22anc simpld ltaddpos mpbid lelttrd breqtrrd
      wceq rmyp1 nn0uz monotuz 3impb ) ADUCUDZEZBFECFEBCGHABIJZACIJZGHUEWCUAUBB
      CAUAUFZIJZWDWEAUBUFZIJZAWHUGUHJZIJZFKWCWHFEZUIZWIWIAUJJZAWHUKJZUHJZWKGWMW
      IWNWPWMLMWIULWLWCWHLEZWILEWHUMZAWHLWBLIUNNOPZWMWIMEZAMEZWNMEZWSWCXAWLDAUO
      UPZWIAUQQZWMXBWOMEZWPMEXDWMFMWOURWLWCWQWOFEWRAWHFWBLUKUSNOPZWNWOUTQWMWTXA
      KWISHZUGASHZWIWNSHWSXCWMKWOGHZXGAWHVAZVBWCXHWLWCATEXHWBTADTEWBTVCVDDVEVFV
      GAVHVIUPWIAVJVKWMXIWNWPGHZWMXIXGXJVLWMXEXBXIXKUEXFXDWOWNVMQVNVOWLWCWQWKWP
      VQWRAWHVROVPWCWFFEZUILMWGULXLWCWFLEWGLEWFUMAWFLWBLIUNNOPVSWFWJAIRWFWHAIRW
      FBAIRWFCAIRVTWA $.
      $( [24-Sep-2014] $)
  $}

  ${
    $d A a b $.  $d M a b $.  $d N a b $.
    $( The X-sequence is strictly monotonic on ` NN0 ` . $)
    ltrmxnn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N
        <-> ( A rmX M ) < ( A rmX N ) ) ) $=
      ( c2 wcel cn0 clt wbr crmx co wb cc0 cr cz fovcl sylan2 sseldi cle oveq2
      cn va vb cuz cfv cv c1 caddc wa cmul nn0ssre nn0z eluzelre adantr remulcl
      frmx syl2anc peano2zdi eluz2b2 simprbi crmy rmxypos simpld ltmulgt11 cexp
      syl3anc mpbid cmin csquarenn cdif rmspecnonsq eldifi syl nnre nn0ge0 3syl
      nnnn0 zssre frmy simprd mulge0 syl22anc addge01 wceq rmxp1 breqtrrd nn0uz
      ltletrd monotuz 3impb ) ADUCUDZEZBFECFEBCGHABIJZACIJZGHKWKUAUBBCAUAUEZIJZ
      WLWMAUBUEZIJZAWPUFUGJZIJZFLWKWPFEZUHZWQWQAUIJZWSXAFMWQUJWTWKWPNEZWQFEWPUK
      ZAWPFWJNIUOOPQZXAWQMEZAMEZXBMEZXEWKXGWTDAULUMZWQAUNUPZXAFMWSUJWTWKWRNEWSF
      EWTWPXDUQAWRFWJNIUOOPQXAUFAGHZWQXBGHZWKXKWTWKATEXKAURUSUMXAXFXGLWQGHZXKXL
      KXEXIXAXMLAWPUTJZRHZAWPVAZVBWQAVCVEVFXAXBXBADVDJUFVGJZXNUIJZUGJZWSRXALXRR
      HZXBXSRHZXAXQMEZLXQRHZXNMEZXOXTXAXQTEZYBWKYEWTWKXQTVHVIEYEAVJXQTVHVKVLUMZ
      XQVMVLZXAYEXQFEYCYFXQVPXQVNVOXANMXNVQWTWKXCXNNEXDAWPNWJNUTVROPQZXAXMXOXPV
      SXQXNVTWAXAXHXRMEZXTYAKXJXAYBYDYIYGYHXQXNUNUPXBXRWBUPVFWTWKXCWSXSWCXDAWPW
      DPWEWGWKWNFEZUHFMWOUJYJWKWNNEWOFEWNUKAWNFWJNIUOOPQWFWNWRAISWNWPAISWNBAISW
      NCAISWHWI $.
      $( [4-Oct-2014] $)

    $( The X-sequence is monotonic on ` NN0 ` . $)
    lermxnn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M <_ N
        <-> ( A rmX M ) <_ ( A rmX N ) ) ) $=
      ( va vb c2 cuz cfv wcel cn0 cle wbr crmx co wb cv oveq2 nn0ssre cz clt wa
      cr nn0z frmx fovcl sylan2 sseldi w3a ltrmxnn0 biimpd 3expb leord1 3impb
      wi ) AFGHZIZBJICJIBCKLABMNZACMNZKLOUPDEADPZMNZAEPZMNZBCJUQURUSVAAMQUSBAMQ
      USCAMQRUPUSJIZUAJUBUTRVCUPUSSIUTJIUSUCAUSJUOSMUDUEUFUGUPVCVAJIZUSVATLZUTV
      BTLZUNUPVCVDUHVEVFAUSVAUIUJUKULUM $.
      $( [4-Oct-2014] $)

    $( The X-sequence is defined to range over ` NN0 ` but never actually takes
       the value 0. $)
    rmxnn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) e. NN ) $=
      ( wcel cz wa cn0 crmx co cn cc0 clt wbr nn0z frmx sylan2 crmy cle rmxypos
      fovcl simpld c2 cuz cfv cneg wo cr elznn0 simprbi adantl elnnnn0b adantlr
      sylanbrc wceq rmxneg adantr eqeltrrd jaodan mpdan ) AUAUBUCZCZBDCZEZBFCZB
      UDZFCZUEZABGHZICZVAVFUTVABUFCVFBUGUHUIVBVCVHVEUTVCVHVAUTVCEZVGFCZJVGKLZVH
      VCUTVAVJBMABFUSDGNSOVIVKJABPHQLABRTVGUJULUKVBVEEAVDGHZVGIVBVLVGUMVEABUNUO
      UTVEVLICZVAUTVEEZVLFCZJVLKLZVMVEUTVDDCVOVDMAVDFUSDGNSOVNVPJAVDPHQLAVDRTVL
      UJULUKUPUQUR $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d M a b $.  $d N a b $.  $d A a b $.
    $( The Y-sequence is strictly monotonic over ` ZZ ` . $)
    ltrmy $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M < N <-> (
        A rmY M ) < ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel crmy co cv cneg cn0 w3a clt wbr ltrmynn0 cz oveq2
      biimpd wa cr zssre frmy fovcl sseldi rmyneg monotoddzz ) AFGHZIZDEBCABJKA
      CJKADLZJKZAELZJKZAUNMZJKUKULNIUNNIOULUNPQUMUOPQAULUNRUAUKULSIUBSUCUMUDAUL
      SUJSJUEUFUGAUNUHULBAJTULCAJTULUNAJTULUPAJTUI $.
      $( [25-Sep-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.
    $( Y is zero only at zero. $)
    rmyeq0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( N = 0 <-> ( A rmY N )
        = 0 ) ) $=
      ( va vb c2 cuz cfv wcel cz wa cc0 wceq crmy co wb cv oveq2 zssre clt wbr
      0z cr frmy fovcl sseldi wi ltrmy biimpd 3expb eqord1 mpanr2 adantr eqeq2d
      w3a rmy0 bitrd ) AEFGZHZBIHZJZBKLZABMNZAKMNZLZVBKLURUSKIHVAVDOUAURCDACPZM
      NZADPZMNZBKIVBVCVEVGAMQVEBAMQVEKAMQRURVEIHZJIUBVFRAVEIUQIMUCUDUEURVIVGIHZ
      VEVGSTZVFVHSTZUFURVIVJUNVKVLAVEVGUGUHUIUJUKUTVCKVBURVCKLUSAUOULUMUP $.
      $( [26-Sep-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.  $d M a b $.
    $( Y is one-to-one. $)
    rmyeq $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M = N <-> (
        A rmY M ) = ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel cz wceq crmy co wb cv oveq2 zssre wa clt wbr frmy
      cr fovcl sseldi wi w3a ltrmy biimpd 3expb eqord1 3impb ) AFGHZIZBJICJIBCK
      ABLMZACLMZKNUMDEADOZLMZAEOZLMZBCJUNUOUPURALPUPBALPUPCALPQUMUPJIZRJUBUQQAU
      PJULJLUAUCUDUMUTURJIZUPURSTZUQUSSTZUEUMUTVAUFVBVCAUPURUGUHUIUJUK $.
      $( [3-Oct-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.  $d M a b $.
    $( Y is monotonic (non-strict). $)
    lermy $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> (
        A rmY M ) <_ ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel cz cle wbr crmy co wb cv oveq2 zssre wa clt fovcl
      cr frmy sseldi wi w3a ltrmy biimpd 3expb leord1 3impb ) AFGHZIZBJICJIBCKL
      ABMNZACMNZKLOUMDEADPZMNZAEPZMNZBCJUNUOUPURAMQUPBAMQUPCAMQRUMUPJIZSJUBUQRA
      UPJULJMUCUAUDUMUTURJIZUPURTLZUQUSTLZUEUMUTVAUFVBVCAUPURUGUHUIUJUK $.
      $( [3-Oct-2014] $)
  $}
  $( PLEASE PUT DESCRIPTION HERE. $)
  rmynn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( A rmY N ) e. NN ) $=
    ( c2 cuz cfv wcel cn wa crmy co cz cc0 clt wbr nnz frmy fovcl sylan2 adantl
    wceq rmy0 adantr nngt0 wb simpl ltrmy syl3anc mpbid eqbrtrrd elnnz sylanbrc
    0z a1i ) ACDEZFZBGFZHZABIJZKFZLURMNURGFUPUOBKFZUSBOZABKUNKIPQRUQALIJZLURMUO
    VBLTUPAUAUBUQLBMNZVBURMNZUPVCUOBUCSUQUOLKFZUTVCVDUDUOUPUEVEUQULUMUPUTUOVASA
    LBUFUGUHUIURUJUK $.

  $( [16-Oct-2014] $)
  rmynn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY N ) e. NN0 ) $=
    ( c2 cuz cfv wcel cn0 wa crmy co cz cc0 cle wbr nn0z frmy fovcl sylan2 crmx
    clt rmxypos simprd elnn0z sylanbrc ) ACDEZFZBGFZHZABIJZKFZLUIMNZUIGFUGUFBKF
    UJBOABKUEKIPQRUHLABSJTNUKABUAUBUIUCUD $.
    $( [16-Oct-2014] $)

  ${
    $d A a b $.  $d B a b $.
    $( ` rmY ` commutes with ` abs ` . $)
    rmyabs $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ZZ ) -> ( abs ` ( A rmY B ) ) =
        ( A rmY ( abs ` B ) ) ) $=
      ( va vb c2 cuz cfv wcel cv crmy co cneg cabs cz wa cr cc0 cle wbr oveq2
      zssre frmy fovcl sseldi w3a crmx clt simp1 elnn0z biimpri 3adant1 rmxypos
      cn0 syl2anc simprd rmyneg oddcomabszz ) AEFGZHZCDACIZJKZADIZJKAVBLZJKBABJ
      KABMGZJKUSUTNHZONPVAUAAUTNURNJUBUCUDUSVEQUTRSZUEZQAUTUFKUGSZQVARSZVGUSUTU
      MHZVHVIOUSVEVFUHVEVFVJUSVJVEVFOUTUIUJUKAUTULUNUOAVBUPUTVBAJTUTVCAJTUTBAJT
      UTVDAJTUQ $.
      $( [26-Sep-2014] $)
  $}

  $( X(n) is strictly greater than Y(n) + Y(n-1).  Lemma 2.24 of
     [JonesMatijasevic] restricted to ` NN ` . $)
  jm2.24nn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( ( A rmY ( N - 1 ) ) +
      ( A rmY N ) ) < ( A rmX N ) ) $=
    ( c2 wcel c1 cmin co crmy cr cz sylan2 syl2anc cn0 clt wbr cc wceq wb mpbid
    cc0 cuz cfv cn wa caddc cmul crmx zssre 1z zsubcl sylancl frmy fovcl sseldi
    nnz readdcl 2re remulcl sylancr resubcl nn0ssre eluzelre adantr cle nnm1nn0
    a1i rmxypos simprd jca eluzle lemul1a syl31anc recnd mulcom simpld ltaddpos
    frmx eqbrtrd lelttrd 2times rmyp1 adantl ax-1cn npcan oveq2d eqtr3d 3brtr3d
    syl nnre ltaddsub syl3anc ltadd1 oveq1d addsub eqtrd breqtrrd rmy0 nngt0 0z
    simpl ltrmy eqbrtrrd lemul1 syl112anc lesub1 rmym1 eqcomd subsub23 ltletrd
    ) ACUAUBZDZBUCDZUDZABEFGZHGZABHGZUEGZCXPUFGZXOFGZABUGGZXMXOIDZXPIDZXQIDXMJI
    XOUHXLXKXNJDZXOJDXLBJDZEJDYCBUOZUIBEUJUKZAXNJXJJHULUMKUNZXMJIXPUHXLXKYDXPJD
    YEABJXJJHULUMKUNZXOXPUPLXMXRIDZYAXSIDXMCIDZYBYIUQYHCXPURUSZYGXRXOUTLXMMIXTV
    AXLXKYDXTMDYEABMXJJUGVQUMKUNZXMXQXPXOFGZXPUEGZXSNXMXOYMNOZXQYNNOZXMXOXOUEGZ
    XPNOZYOXMCXOUFGZXOAUFGZAXNUGGZUEGZYQXPNXMYSAXOUFGZUUBXMYJYAYSIDUQYGCXOURUSX
    MAIDZYAUUCIDXKUUDXLCAVBVCZYGAXOURLXMYTIDZUUAIDZUUBIDXMYAUUDUUFYGUUEXOAURLZX
    MMIUUAVAXLXKYCUUAMDYFAXNMXJJUGVQUMKUNZYTUUAUPLXMYJUUDYATXOVDOZUDCAVDOZYSUUC
    VDOYJXMUQVFZUUEXMYAUUJYGXLXKXNMDZUUJBVEZXKUUMUDZTUUANOZUUJAXNVGZVHKVIXKUUKX
    LCAVJVCZCAXOVKVLXMUUCYTUUBNXMAPDZXOPDZUUCYTQXMAUUEVMZXMXOYGVMZAXOVNLXMUUPYT
    UUBNOZXLXKUUMUUPUUNUUOUUPUUJUUQVOKXMUUGUUFUUPUVCRUUIUUHUUAYTVPLSVRVSXMUUTYS
    YQQUVBXOVTWHXMAXNEUEGZHGZUUBXPXLXKYCUVEUUBQYFAXNWAKXMUVDBAHXMBPDEPDUVDBQXMB
    XLBIDXKBWIWBVMWCBEWDUKWEWFWGXMYAYAYBYRYORYGYGYHXOXOXPWJWKSXMYAYMIDZYBYOYPRY
    GXMYBYAUVFYHYGXPXOUTLYHXOYMXPWLWKSXMXSXPXPUEGZXOFGZYNXMXRUVGXOFXMXPPDZXRUVG
    QXMXPYHVMZXPVTWHWMXMUVIUVIUUTUVHYNQUVJUVJUVBXPXPXOWNWKWOWPXMXSAXPUFGZXOFGZX
    TVDXMXRUVKVDOZXSUVLVDOZXMUUKUVMUURXMYJUUDYBTXPNOUUKUVMRUULUUEYHXMATHGZTXPNX
    KUVOTQXLAWQVCXMTBNOZUVOXPNOZXLUVPXKBWRWBXMXKTJDZYDUVPUVQRXKXLWTUVRXMWSVFXLY
    DXKYEWBATBXAWKSXBCAXPXCXDSXMYIUVKIDZYAUVMUVNRYKXMUUDYBUVSUUEYHAXPURLZYGXRUV
    KXOXEWKSXMUVLXTXMUVKXTFGZXOQZUVLXTQZXMXOUWAXMXOXPAUFGZXTFGZUWAXLXKYDXOUWEQY
    EABXFKXMUWDUVKXTFXMUVIUUSUWDUVKQUVJUVAXPAVNLWMWOXGXMUVKPDXTPDUUTUWBUWCRXMUV
    KUVTVMXMXTYLVMUVBUVKXTXOXHWKSXGWPXI $.
    $( [3-Oct-2014] $)

  ${
    $d A a b $.  $d N a b $.
    $( Lemma 2.17 of [JonesMatijasevic], left side. $)
    jm2.17a $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( ( ( 2 x. A ) - 1 ) ^
        N ) <_ ( A rmY ( N + 1 ) ) ) $=
      ( wcel c2 cmul co c1 cmin cexp caddc crmy cle wbr wi cc0 cc cz cr syl2anc
      wceq va vb cn0 cuz cfv cv oveq2 oveq1 oveq2d breq12d imbi2d weq 1re leidi
      a1i 2cn eluzelz zcn syl mulcl sylancr ax-1cn subcl sylancl addid2i oveq2i
      exp0 rmy1 syl5eq 3brtr4d w3a wa eluzelre adantl remulcl resubcl peano2nn0
      2re adantr reexpcl 3adant3 simpr nn0z peano2zdi zssre frmy fovcl 3ad2ant2
      sseldi simp1 expp1 cn 2nn clt eluz2b2 simplbi nnmulcl nnm1nn0 nn0ge0 3syl
      simpl jca 3jca simp3 lemul1a eqbrtrd nn0re lep1 lermy syl3anc mpbid nn0cn
      pncan recnd mulid1 eqeltrd lesub2 subdi mulcom oveq1d eqtrd rmyluc2 letrd
      wb 3exp a2d nn0ind impcom ) BUCCADUDUEZCZDAEFZGHFZBIFZABGJFZKFZLMZYJYLUAU
      FZIFZAYQGJFZKFZLMZNYJYLOIFZAOGJFZKFZLMZNYJYLUBUFZIFZAUUFGJFZKFZLMZNYJYLUU
      HIFZAUUHGJFZKFZLMZNYJYPNUAUBBYQOTZUUAUUEYJUUOYRUUBYTUUDLYQOYLIUGUUOYSUUCA
      KYQOGJUHUIUJUKUAUBULZUUAUUJYJUUPYRUUGYTUUILYQUUFYLIUGUUPYSUUHAKYQUUFGJUHU
      IUJUKYQUUHTZUUAUUNYJUUQYRUUKYTUUMLYQUUHYLIUGUUQYSUULAKYQUUHGJUHUIUJUKYQBT
      ZUUAYPYJUURYRYMYTYOLYQBYLIUGUURYSYNAKYQBGJUHUIUJUKYJGGUUBUUDLGGLMYJGUMUNU
      OYJYLPCZUUBGTYJYKPCZGPCZUUSYJDPCAPCZUUTUPYJAQCUVBDAUQAURUSDAUTVAVBYKGVCVD
      ZYLVGUSYJUUDAGKFGUUCGAKGVBVEVFAVHVIVJUUFUCCZYJUUJUUNUVDYJUUJUUNUVDYJUUJVK
      ZUUKUUIYLEFZUUMUVDYJUUKRCZUUJUVDYJVLZYLRCZUUHUCCZUVGUVHYKRCZGRCZUVIUVHDRC
      ARCZUVKVRYJUVMUVDDAVMVNDAVOVAZUMYKGVPVDZUVDUVJYJUUFVQVSYLUUHVTSWAUVDYJUVF
      RCZUUJUVHUUIRCZUVIUVPUVHYJUUHQCZUVQUVDYJWBZUVHUUFUVDUUFQCZYJUUFWCVSZWDZYJ
      UVRVLQRUUIWEAUUHQYIQKWFWGWISZUVOUUIYLVOSWAUVDYJUUMRCZUUJUVHYJUULQCZUWDUVS
      UVHUUHUWBWDYJUWEVLQRUUMWEAUULQYIQKWFWGWISWAUVEUUKUUGYLEFZUVFLUVEUUSUVDUUK
      UWFTYJUVDUUSUUJUVCWHUVDYJUUJWJYLUUFWKSUVEUUGRCZUVQUVIOYLLMZVLZVKZUUJUWFUV
      FLMUVDYJUWJUUJUVHUWGUVQUWIUVHUVIUVDUWGUVOUVDYJXAYLUUFVTSUWCUVHUVIUWHUVOUV
      HYKWLCZYLUCCUWHUVHDWLCAWLCZUWKWMYJUWLUVDYJUWLGAWNMAWOWPVNDAWQVAYKWRYLWSWT
      XBXCWAUVDYJUUJXDUUGUUIYLXESXFUVDYJUVFUUMLMUUJUVHYKUUIEFZUUIGEFZHFZUWMAUUH
      GHFZKFZHFZUVFUUMLUVHUWQUWNLMZUWOUWRLMZUVHAUUFKFZUUIUWQUWNLUVHUUFUUHLMZUXA
      UUILMZUVHUUFRCZUXBUVDUXDYJUUFXGVSUUFXHUSUVHYJUVTUVRUXBUXCYDUVSUWAUWBAUUFU
      UHXIXJXKUVHUWPUUFAKUVHUUFPCZUVAUWPUUFTUVDUXEYJUUFXLVSVBUUFGXMVDUIZUVHUUIP
      CZUWNUUITUVHUUIUWCXNZUUIXOUSVJUVHUWQRCUWNRCZUWMRCZUWSUWTYDUVHUWQUXARUXFUV
      HYJUVTUXARCUVSUWAYJUVTVLQRUXAWEAUUFQYIQKWFWGWISXPUVHUVQUVLUXIUWCUMUUIGVOV
      DUVHUVKUVQUXJUVNUWCYKUUIVOSUWQUWNUWMXQXJXKUVHUVFUUIYKEFZUWNHFZUWOUVHUXGUU
      TUVAUVFUXLTUXHUVHYKUVNXNZUVAUVHVBUOUUIYKGXRXJUVHUXKUWMUWNHUVHUXGUUTUXKUWM
      TUXHUXMUUIYKXSSXTYAUVHYJUVRUUMUWRTUVSUWBAUUHYBSVJWAYCYEYFYGYH $.
      $( [14-Oct-2014] $)

    $( Lemma 2.17 of [JonesMatijasevic], right side.  A weaker form of the
       bound which allows induction to start lower. $)
    jm2.17b $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY ( N + 1 ) )
        <_ ( ( 2 x. A ) ^ N ) ) $=
      ( wcel c2 c1 caddc co crmy cmul cexp cle wbr wi wceq oveq2d cr wa syl2anc
      cc0 cz va vb cn0 cuz cfv cv oveq1 oveq2 breq12d imbi2d weq 1re a1i ax-1cn
      leidi addid2i oveq2i rmy1 syl5eq cc 2re eluzelre remulcl sylancr exp0 syl
      recnd 3brtr4d w3a cmin simpr nn0z adantr peano2zdi rmyluc2 rmxypos simprd
      crmx clt ancoms nn0re pncan sylancl breqtrrd wb adantl zssre fovcl sseldi
      frmy eqeltrd subge02 mpbid eqbrtrd 3adant3 reexpcl cn 2nn eluz2b2 simplbi
      simpl nnmulcl nngt0 lemul2 syl112anc biimp3a expp1 mulcom eqtrd peano2nn0
      letr syl3anc mp2and 3exp a2d nn0ind impcom ) BUCCADUDUEZCZABEFGZHGZDAIGZB
      JGZKLZXSAUAUFZEFGZHGZYBYEJGZKLZMXSASEFGZHGZYBSJGZKLZMXSAUBUFZEFGZHGZYBYNJ
      GZKLZMXSAYOEFGZHGZYBYOJGZKLZMXSYDMUAUBBYESNZYIYMXSUUCYGYKYHYLKUUCYFYJAHYE
      SEFUGOYESYBJUHUIUJUAUBUKZYIYRXSUUDYGYPYHYQKUUDYFYOAHYEYNEFUGOYEYNYBJUHUIU
      JYEYONZYIUUBXSUUEYGYTYHUUAKUUEYFYSAHYEYOEFUGOYEYOYBJUHUIUJYEBNZYIYDXSUUFY
      GYAYHYCKUUFYFXTAHYEBEFUGOYEBYBJUHUIUJXSEEYKYLKEEKLXSEULUOUMXSYKAEHGEYJEAH
      EUNUPUQAURUSXSYBUTCZYLENXSYBXSDPCZAPCZYBPCZVADAVBZDAVCZVDVGYBVEVFVHYNUCCZ
      XSYRUUBUUMXSYRUUBUUMXSYRVIZYTYBYPIGZKLZUUOUUAKLZUUBUUMXSUUPYRUUMXSQZYTUUO
      AYOEVJGZHGZVJGZUUOKUURXSYOTCZYTUVANUUMXSVKZUURYNUUMYNTCZXSYNVLVMZVNZAYOVO
      RUURSUUTKLZUVAUUOKLZUURSAYNHGZUUTKXSUUMSUVIKLZXSUUMQSAYNVRGVSLUVJAYNVPVQV
      TUURUUSYNAHUURYNUTCEUTCUUSYNNUURYNUUMYNPCXSYNWAVMVGUNYNEWBWCOZWDUURUUOPCZ
      UUTPCUVGUVHWEUURUUJYPPCZUVLUURUUHUUIUUJVAXSUUIUUMUUKWFUULVDZUURXSUVBUVMUV
      CUVFXSUVBQTPYPWGAYOTXRTHWJWHWIRZYBYPVCRZUURUUTUVIPUVKUURXSUVDUVIPCUVCUVEX
      SUVDQTPUVIWGAYNTXRTHWJWHWIRWKUUOUUTWLRWMWNWOUUNUUOYBYQIGZUUAKUUMXSYRUUOUV
      QKLZUURUVMYQPCZUUJSYBVSLZYRUVRWEUVOUURUUJUUMUVSUVNUUMXSXAZYBYNWPRZUVNXSUV
      TUUMXSYBWQCZUVTXSDWQCAWQCZUWCWRXSUWDEAVSLAWSWTDAXBVDYBXCVFWFYPYQYBXDXEXFU
      UMXSUUAUVQNYRUURUUAYQYBIGZUVQUURUUGUUMUUAUWENUURYBUVNVGZUWAYBYNXGRUURYQUT
      CUUGUWEUVQNUURYQUWBVGUWFYQYBXHRXIWOWDUUMXSUUPUUQQUUBMZYRUURYTPCZUVLUUAPCZ
      UWGUURXSYSTCZUWHUVCUURYOUVFVNXSUWJQTPYTWGAYSTXRTHWJWHWIRUVPUURUUJYOUCCZUW
      IUVNUUMUWKXSYNXJVMYBYOWPRYTUUOUUAXKXLWOXMXNXOXPXQ $.
      $( [15-Oct-2014] $)

  $}

  $( Lemma 2.17 of [JonesMatijasevic], right side. $)
  jm2.17c $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) ->
      ( A rmY ( ( N + 1 ) + 1 ) ) < ( ( 2 x. A ) ^ ( N + 1 ) ) ) $=
    ( c2 wcel cn wa cmul co c1 crmy clt cr adantr cz adantl syl2anc cc wceq cc0
    wbr cuz cfv caddc cmin cexp 2re eluzelre remulcl sylancr nnz peano2zdi frmy
    simpl zssre fovcl sseldi ax-1cn pncan sylancl oveq2d sylan2 eqeltrd resubcl
    nncn cn0 nnnn0 reexpcl rmy0 nngt0 wb 0z a1i ltrmy syl3anc eqbrtrrd breqtrrd
    mpbid ltsubpos cle jm2.17b 2nn eluz2b2 simplbi nnmulcl syl lemul2 syl112anc
    ltletrd rmyluc2 recnd expp1 mulcom eqtrd 3brtr4d ) ACUAUBZDZBEDZFZCAGHZABIU
    CHZJHZGHZAWTIUDHZJHZUDHZWSWSBUEHZGHZAWTIUCHJHZWSWTUEHZKWRXEXBXGWRXBLDZXDLDZ
    XELDWRWSLDZXALDZXJWRCLDALDZXLUFWPXNWQCAUGMCAUHUIZWRWPWTNDZXMWPWQUMZWRBWQBND
    ZWPBUJZOZUKZWPXPFNLXAUNAWTNWONJULUOUPPZWSXAUHPZWRXDABJHZLWRXCBAJWRBQDZIQDXC
    BRWQYEWPBVDOUQBIURUSUTZWQWPXRYDLDXSWPXRFNLYDUNABNWONJULUOUPVAVBZXBXDVCPYCWR
    XLXFLDZXGLDXOWRXLBVEDZYHXOWQYIWPBVFOZWSBVGPZWSXFUHPWRSXDKTZXEXBKTZWRSYDXDKW
    RASJHZSYDKWPYNSRWQAVHMWRSBKTZYNYDKTZWQYOWPBVIOWRWPSNDZXRYOYPVJXQYQWRVKVLXTA
    SBVMVNVQVOYFVPWRXKXJYLYMVJYGYCXDXBVRPVQWRXAXFVSTZXBXGVSTZWRWPYIYRXQYJABVTPW
    RXMYHXLSWSKTZYRYSVJYBYKXOWPYTWQWPWSEDZYTWPCEDAEDZUUAWAWPUUBIAKTAWBWCCAWDUIW
    SVIWEMXAXFWSWFWGVQWHWRWPXPXHXERXQYAAWTWIPWRXIXFWSGHZXGWRWSQDZYIXIUUCRWRWSXO
    WJZYJWSBWKPWRXFQDUUDUUCXGRWRXFYKWJUUEXFWSWLPWMWN $.
    $( [15-Oct-2014] $)

  $( Lemma 2.24 of [JonesMatijasevic] extended to ` ZZ ` .  Could be eliminated
     with a more careful proof of ~ jm2.26lem3 . $)
  jm2.24 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmY ( N - 1 ) ) + (
      A rmY N ) ) < ( A rmX N ) ) $=
    ( wcel cz wa cc0 cle wbr c1 co crmy caddc cr fovcl syl2anc sseldi cneg wceq
    clt wb c2 cuz cfv wo cmin crmx zre adantl 0re lelttric sylancl zssre simpll
    peano2zm ad2antlr frmy adantr readdcl a1i cn0 nn0ssre frmx znegcl peano2zdi
    ad2antrr simpr le0neg1 syl mpbid 0z zleltp1 ltrmy syl3anc eqbrtrrd addgtge0
    rmy0 lermy syl22anc cc recnd negdi rmyneg zcn ax-1cn negsubdi oveq2d oveq1d
    oveq12d 3eqtr2d breqtrrd lt0neg1 mpbird ltletrd cn biimpri adantll jm2.24nn
    nn0ge0 elnnz jaodan mpdan ) AUAUBUCZCZBDCZEZBFGHZFBSHZUDZABIUEJZKJZABKJZLJZ
    ABUFJZSHZXEBMCZFMCZXHXDXOXCBUGZUHUIBFUJUKXEXFXNXGXEXFEZXLFXMXRXJMCXKMCZXLMC
    ZXRDMXJULXRXCXIDCZXJDCXCXDXFUMZXDYAXCXFBUNUOZAXIDXBDKUPNOPZXEXSXFXEDMXKULAB
    DXBDKUPNPUQZXJXKUROZXPXRUIUSXRUTMXMVAXEXMUTCZXFABUTXBDUFVBNUQZPXRXLFSHZFXLQ
    ZSHZXRFABQZILJZKJZAYLKJZLJZYJSXRYNMCYOMCFYNSHFYOGHFYPSHXRDMYNULXRXCYMDCZYND
    CYBXRYLXDYLDCZXCXFBVCUOZVDZAYMDXBDKUPNOPXRDMYOULXRXCYRYODCYBYSAYLDXBDKUPNOP
    XRAFKJZFYNSXCUUAFRXDXFAVPVEZXRFYMSHZUUAYNSHZXRFYLGHZUUCXRXFUUEXEXFVFXRXOXFU
    UETXDXOXCXFXQUOBVGVHVIZXRFDCZYRUUEUUCTUUGXRVJUSZYSFYLVKOVIXRXCUUGYQUUCUUDTY
    BUUHYTAFYMVLVMVIVNXRUUAFYOGUUBXRUUEUUAYOGHZUUFXRXCUUGYRUUEUUITYBUUHYSAFYLVQ
    VMVIVNYNYOVOVRXRYJXJQZXKQZLJZAXIQZKJZYOLJYPXRXJVSCXKVSCYJUULRXRXJYDVTXRXKYE
    VTXJXKWAOXRUUNUUJYOUUKLXRXCYAUUNUUJRYBYCAXIWBOXEYOUUKRXFABWBUQWHXRUUNYNYOLX
    RUUMYMAKXRBVSCZIVSCUUMYMRXDUUOXCXFBWCUOWDBIWEUKWFWGWIWJXRXTYIYKTYFXLWKVHWLX
    RYGFXMGHYHXMWRVHWMXEXGEXCBWNCZXNXCXDXGUMXDXGUUPXCUUPXDXGEBWSWOWPABWQOWTXA
    $.
    $( [3-Oct-2014] $)

  ${
    $d A a b $.  $d N a b $.
    $( Y(n) increases faster than n.  Used implicitly without proof or comment
       in [JonesMatijasevic] lemma 2.27; fortunately it is true. $)
    rmygeid $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> N <_ ( A rmY N ) ) $=
      ( va vb wcel co cle wbr wi cc0 c1 id oveq2 breq12d imbi2d cz zssre sseldi
      crmy cr cn0 c2 cuz cfv cv caddc wceq weq 0nn0 nn0ge0i rmy0 syl5breqr nn0z
      w3a 3ad2ant1 peano2zdi simp2 frmy fovcl syl2anc simp3 wb nn0re 1re leadd1
      a1i syl3anc mpbid clt ltp1 syl ltrmy zltp1le letrd 3exp a2d nn0ind impcom
      ) BUAEAUBUCUDZEZBABSFZGHZVTCUEZAWCSFZGHZIVTJAJSFZGHZIVTDUEZAWHSFZGHZIVTWH
      KUFFZAWKSFZGHZIVTWBICDBWCJUGZWEWGVTWNWCJWDWFGWNLWCJASMNOCDUHZWEWJVTWOWCWH
      WDWIGWOLWCWHASMNOWCWKUGZWEWMVTWPWCWKWDWLGWPLWCWKASMNOWCBUGZWEWBVTWQWCBWDW
      AGWQLWCBASMNOVTJJWFGJUIUJAUKULWHUAEZVTWJWMWRVTWJWMWRVTWJUNZWKWIKUFFZWLWSP
      TWKQWSWHWRVTWHPEZWJWHUMUOZUPZRWSPTWTQWSWIWSVTXAWIPEZWRVTWJUQZXBAWHPVSPSUR
      USUTZUPRWSPTWLQWSVTWKPEZWLPEZXEXCAWKPVSPSURUSUTZRWSWJWKWTGHZWRVTWJVAWSWHT
      EZWITEKTEZWJXJVBWRVTXKWJWHVCUOZWSPTWIQXFRXLWSVDVFWHWIKVEVGVHWSWIWLVIHZWTW
      LGHZWSWHWKVIHZXNWSXKXPXMWHVJVKWSVTXAXGXPXNVBXEXBXCAWHWKVLVGVHWSXDXHXNXOVB
      XFXIWIWLVMUTVHVNVOVPVQVR $.
      $( [4-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Congruential equations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A wff of the form ` A || ( B - C ) ` is interpreted as a congruential
     equation.  This is similar to ` ( B mod A ) = ( C mod A ) ` , but is
     defined such that behavior is regular for zero and negative values of
     ` A ` .  To use this concept effectively, we need to show that
     congruential equations behave similarly to normal equations; first a
     transitivity law.  Idea for the future:  If there was a congruential
     equation symbol, it could incorporate type constraints, so that most of
     these would not need them. $)
  congtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A || (
      B - C ) /\ A || ( C - D ) ) ) -> A || ( B - D ) ) $=
    ( cz wcel wa co cdivides wbr w3a caddc simp1l simp1r zsubcl 3ad2ant2 cc zcn
    cmin adantl simp2l syl2anc simp3 dvds2add imp syl31anc wceq 3ad2ant1 adantr
    npncan syl3anc breqtrd ) AEFZBEFZGZCEFZDEFZGZABCSHZIJACDSHZIJGZKZAUSUTLHZBD
    SHZIVBUMUSEFZUTEFZVAAVCIJZUMUNURVAMVBUNUPVEUMUNURVANUOUPUQVAUABCOUBURUOVFVA
    CDOPUOURVAUCUMVEVFKVAVGAUSUTUDUEUFVBBQFZCQFZDQFZVCVDUGUOURVHVAUNVHUMBRTUHUR
    UOVIVAUPVIUQCRUIPURUOVJVAUQVJUPDRTPBCDUJUKUL $.
    $( [1-Oct-2014] $)

  $( If two pairs of numbers are componentwise congruent, so are their sums. $)
  congadd $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B + D ) - ( C + E )
      ) ) $=
    ( cz wcel w3a wa cmin co cdivides wbr caddc wi simpl1 zsubcl cc zcn syl
    3adant1 adantr adantl dvds2add syl3anc 3impia wceq simpl2 ad2antrl ad2antll
    simpl3 addsub4 syl22anc 3adant3 breqtrrd ) AFGZBFGZCFGZHZDFGZEFGZIZABCJKZLM
    ADEJKZLMIZHAVCVDNKZBDNKCENKJKZLUSVBVEAVFLMZUSVBIZUPVCFGZVDFGZVEVHOUPUQURVBP
    USVJVBUQURVJUPBCQUAUBVBVKUSDEQUCAVCVDUDUEUFUSVBVGVFUGZVEVIBRGZDRGZCRGZERGZV
    LVIUQVMUPUQURVBUHBSTUTVNUSVADSUIVIURVOUPUQURVBUKCSTVAVPUSUTESUJBDCEULUMUNUO
    $.
    $( [1-Oct-2014] $)

  $( If two pairs of numbers are componentwise congruent, so are their
     products. $)
  congmul $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B x. D ) - ( C x. E
      ) ) ) $=
    ( cz wcel w3a wa cmin cdivides wbr cmul zmulcl syl2anc 3ad2ant2 syl3anc zcn
    co cc simp11 simp12 simp2l simp2r simp13 simp3r wi dvdsmultr2 wceq 3ad2ant1
    zsubcl adantr adantl subdi breqtrd simp3l dvdsmultr1 3ad2ant3 subdir congtr
    mpd syl222anc ) AFGZBFGZCFGZHZDFGZEFGZIZABCJSZKLZADEJSZKLZIZHZVCBDMSZFGZBEM
    SZFGZCEMSZFGZAVPVRJSZKLAVRVTJSZKLAVPVTJSKLVCVDVEVIVNUAZVOVDVGVQVCVDVEVIVNUB
    ZVFVGVHVNUCBDNOVOVDVHVSWEVFVGVHVNUDZBENOVOVEVHWAVCVDVEVIVNUEZWFCENOVOABVLMS
    ZWBKVOVMAWHKLZVFVIVKVMUFVOVCVDVLFGZVMWIUGWDWEVIVFWJVNDEUKPABVLUHQVAVOBTGZDT
    GZETGZWHWBUIVFVIWKVNVDVCWKVEBRPUJZVIVFWLVNVGWLVHDRULPVIVFWMVNVHWMVGERUMPZBD
    EUNQUOVOAVJEMSZWCKVOVKAWPKLZVFVIVKVMUPVOVCVJFGZVHVKWQUGWDVOVDVEWRWEWGBCUKOW
    FAVJEUQQVAVOWKCTGZWMWPWCUIWNVFVIWSVNVEVCWSVDCRURUJWOBCEUSQUOAVPVRVTUTVB $.
    $( [1-Oct-2014] $)

  $( Congruence mod ` A ` is a symmetric/commutative relation. $)
  congsym $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( C - B ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg simprr cc wceq zcn ad2antrl ad2antlr
    negsubdi2 syl2anc breqtrrd wb simpll simprl simplr zsubcl dvdsnegb mpbird )
    ADEZBDEZFZCDEZABCGHZIJZFZFZACBGHZIJZAUPKZIJZUOAULURIUJUKUMLUOCMEZBMEZURULNU
    KUTUJUMCOPUIVAUHUNBOQCBRSTUOUHUPDEZUQUSUAUHUIUNUBUOUKUIVBUJUKUMUCUHUIUNUDCB
    UESAUPUFSUG $.
    $( [1-Oct-2014] $)

  $( If two integers are congruent mod ` A ` , so are their negatives. $)
  congneg $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( -u B - -u C ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg congsym wceq cc zcn syl2an ad2ant2lr
    neg2sub breqtrrd ) ADEZBDEZFCDEZABCGHIJZFFACBGHZBKCKGHZIABCLUAUBUEUDMZTUCUA
    BNECNEUFUBBOCOBCRPQS $.
    $( [1-Oct-2014] $)

  $( If two pairs of numbers are componentwise congruent, so are their
     differences. $)
  congsub $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B - D ) - ( C - E )
      ) ) $=
    ( cz wcel w3a wa cmin co cdivides wbr cneg caddc znegcl syl cc zsscn sseldi
    simp11 simp12 simp13 simp2l simp2r simp3l simp3r congneg syl22anc syl322anc
    congadd wceq negsub syl2anc oveq12d breqtrd ) AFGZBFGZCFGZHZDFGZEFGZIZABCJK
    LMZADEJKLMZIZHZABDNZOKZCENZOKZJKZBDJKZCEJKZJKLVGUQURUSVHFGZVJFGZVDAVHVJJKLM
    ZAVLLMUQURUSVCVFUAZUQURUSVCVFUBZUQURUSVCVFUCZVGVAVOUTVAVBVFUDZDPQVGVBVPUTVA
    VBVFUEZEPQUTVCVDVEUFVGUQVAVBVEVQVRWAWBUTVCVDVEUGADEUHUIABCVHVJUKUJVGVIVMVKV
    NJVGBRGDRGVIVMULVGFRBSVSTVGFRDSWATBDUMUNVGCRGERGVKVNULVGFRCSVTTVGFRESWBTCEU
    MUNUOUP $.
    $( [2-Oct-2014] $)

  $( Every integer is congruent to itself mod every base. $)
  congid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> A || ( B - B ) ) $=
    ( cz wcel wa cc0 cmin co cdivides wbr dvds0 adantr cc wceq zcn adantl subid
    syl breqtrrd ) ACDZBCDZEZAFBBGHZITAFIJUAAKLUBBMDZUCFNUAUDTBOPBQRS $.
    $( [1-Oct-2014] $)

  ${
    $d F a b c $.  $d X a b c k $.  $d V a b c k $.  $d Y a b c k $.
    $d N a b c k $.

    $( Polynomials commute with congruences.  (Does this characterize them?) $)
    mzpcong $p |- ( ( F e. ( mzPoly ` V ) /\ ( X e. ( ZZ ^m V ) /\ Y e. ( ZZ ^m
        V ) ) /\ ( N e. ZZ /\ A. k e. V N || ( ( X ` k ) - ( Y ` k ) ) ) ) -> N
        || ( ( F ` X ) - ( F ` Y ) ) ) $=
      ( vc cfv wcel cz cmin cdivides wbr cvv syl2anc wceq oveq12d breq2d fveq1
      co va vb cmzp cmap wa cv wral w3a cdm elfvdm dmmzp syl6eleq 3anim1i simp1
      csn cxp cmpt caddc cof cmul simpl3l simpr congid simpl2l vex fvconst2 syl
      simpl2r breqtrrd simpl3r weq fveq2 rcla4va eqid fvex fvmpt simp13l simp2l
      wf simp12l ffvelrn simp12r simp3l simp2r simp3r congadd syl322anc wfn ffn
      ovex a1i fnfvof syl22anc congmul mzpindd ) BDUCHIZEJDUDTZIZFWQIZUEZCJIZCA
      UFZEHZXBFHZKTZLMZADUGZUEZUHDNIZWTXHUHZWPCEBHZFBHZKTZLMZWPXIWTXHWPDUCUINBD
      UCUJUKULUMWPWTXHUNXJCEUAUFZHZFXOHZKTZLMCEWQUBUFZUOUPZHZFXTHZKTZLMCEGWQXSG
      UFZHZUQZHZFYFHZKTZLMCEXSHZFXSHZKTZLMZCEYDHZFYDHZKTZLMZCEXSYDURUSTZHZFYRHZ
      KTZLMCEXSYDUTUSTZHZFUUBHZKTZLMXNUABUBGDXJXSJIZUEZCXSXSKTZYCLUUGXAUUFCUUHL
      MXAXGXIWTUUFVAXJUUFVBCXSVCOUUGYAXSYBXSKUUGWRYAXSPWRWSXIXHUUFVDWQXSEUBVEZV
      FVGUUGWSYBXSPWRWSXIXHUUFVHWQXSFUUIVFVGQVIXJXSDIZUEZCXSEHZXSFHZKTZYILUUKUU
      JXGCUUNLMZXJUUJVBXAXGXIWTUUJVJXFUUOAXSDAUBVKZXEUUNCLUUPXCUULXDUUMKXBXSEVL
      XBXSFVLQRVMOUUKYGUULYHUUMKUUKWRYGUULPWRWSXIXHUUJVDGEYEUULWQYFXSYDESYFVNZX
      SEVOVPVGUUKWSYHUUMPWRWSXIXHUUJVHGFYEUUMWQYFXSYDFSUUQXSFVOVPVGQVIXJWQJXSVS
      ZYMUEZWQJYDVSZYQUEZUHZCYJYNURTZYKYOURTZKTZUUALUVBXAYJJIZYKJIZYNJIZYOJIZYM
      YQCUVELMXAXGXIWTUUSUVAVQZUVBUURWRUVFXJUURYMUVAVRZWRWSXIXHUUSUVAVTZWQJEXSW
      AOZUVBUURWSUVGUVKWRWSXIXHUUSUVAWBZWQJFXSWAOZUVBUUTWRUVHXJUUSUUTYQWCZUVLWQ
      JEYDWAOZUVBUUTWSUVIUVPUVNWQJFYDWAOZXJUURYMUVAWDZXJUUSUUTYQWEZCYJYKYNYOWFW
      GUVBYSUVCYTUVDKUVBXSWQWHZYDWQWHZWQNIZWRYSUVCPUVBUURUWAUVKWQJXSWIVGZUVBUUT
      UWBUVPWQJYDWIVGZUWCUVBJDUDWJWKZUVLWQURXSYDNEWLWMUVBUWAUWBUWCWSYTUVDPUWDUW
      EUWFUVNWQURXSYDNFWLWMQVIUVBCYJYNUTTZYKYOUTTZKTZUUELUVBXAUVFUVGUVHUVIYMYQC
      UWILMUVJUVMUVOUVQUVRUVSUVTCYJYKYNYOWNWGUVBUUCUWGUUDUWHKUVBUWAUWBUWCWRUUCU
      WGPUWDUWEUWFUVLWQUTXSYDNEWLWMUVBUWAUWBUWCWSUUDUWHPUWDUWEUWFUVNWQUTXSYDNFW
      LWMQVIXOXTPZXRYCCLUWJXPYAXQYBKEXOXTSFXOXTSQRXOYFPZXRYICLUWKXPYGXQYHKEXOYF
      SFXOYFSQRUAUBVKZXRYLCLUWLXPYJXQYKKEXOXSSFXOXSSQRUAGVKZXRYPCLUWMXPYNXQYOKE
      XOYDSFXOYDSQRXOYRPZXRUUACLUWNXPYSXQYTKEXOYRSFXOYRSQRXOUUBPZXRUUECLUWOXPUU
      CXQUUDKEXOUUBSFXOUUBSQRXOBPZXRXMCLUWPXPXKXQXLKEXOBSFXOBSQRWOO $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d A a $.  $d N a $.
    $( Every integer is congruent to some number in the fundamental domain. $)
    congrep $p |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... ( A - 1 ) ) A ||
        ( a - N ) ) $=
      ( cn wcel cz wa cmo co cc0 c1 cmin cfz cdivides wbr ancoms adantr syl2anc
      cv cn0 wrex zmodfz nnz simpr nn0ssz zmodcl sseldi cdiv cr crp zre moddifz
      nnrp syl2anr wne wb nnne0 zsubcl divides2 syl3anc mpbird congsym syl22anc
      wceq oveq1 breq2d rcla4ev ) ADEZBFEZGZBAHIZJAKLIMIZEZAVKBLIZNOZACSZBLIZNO
      ZCVLUAVIVHVMBAUBPVJAFEZVIVKFEZABVKLIZNOZVOVHVSVIAUCQZVHVIUDZVJTFVKUEVIVHV
      KTEBAUFPUGZVJWBWAAUHIFEZVIBUIEAUJEWFVHBUKAUMBAULUNVJVSAJUOZWAFEZWBWFUPWCV
      HWGVIAUQQVJVIVTWHWDWEBVKURRAWAUSUTVAABVKVBVCVRVOCVKVLVPVKVDVQVNANVPVKBLVE
      VFVGR $.
      $( [2-Oct-2014] $)
  $}

  $( If two integers are congruent, they are either equal or separated by at
     least the congruence base. $)
  congabseq $p |- ( ( ( A e. NN /\ B e. ZZ /\ C e. ZZ ) /\ A || ( B - C ) ) ->
      ( ( abs ` ( B - C ) ) < A <-> B = C ) ) $=
    ( wcel cz w3a cmin co wbr wa cabs cfv clt wceq cc0 cr zcn 3ad2ant1 ad2antrr
    cc cn cdivides cle wn wb zsubcl 3adant1 abscl 3syl adantr nnre ltnle biimpa
    syl2anc wne nnz ad3antrrr simpr 3jca simpllr dvdsleabs sylc ex necon1bd mpd
    3ad2ant2 3ad2ant3 subeq0 mpbid oveq1 adantl subid eqtrd fveq2d syl6eq nngt0
    syl abs0 eqbrtrd impbida ) AUADZBEDZCEDZFZABCGHZUBIZJZWEKLZAMIZBCNZWGWIJZWE
    ONZWJWKAWHUCIZUDZWLWGWIWNWGWHPDZAPDZWIWNUEWDWOWFWDWEEDZWETDWOWBWCWQWABCUFUG
    ZWEQWEUHUIUJWDWPWFWAWBWPWCAUKRUJWHAULUNUMWKWMWEOWKWEOUOZWMWKWSJZAEDZWQWSFWF
    WMWTXAWQWSWDXAWFWIWSWAWBXAWCAUPRUQWDWQWFWIWSWRUQWKWSURUSWDWFWIWSUTAWEVAVBVC
    VDVEWKBTDZCTDZWLWJUEWDXBWFWIWBWAXBWCBQVFSWDXCWFWIWCWAXCWBCQVGZSBCVHUNVIWGWJ
    JZWHOAMXEWHOKLOXEWEOKXEWECCGHZOWJWEXFNWGBCCGVJVKXEXCXFONWDXCWFWJXDSCVLVQVMV
    NVRVOWDOAMIZWFWJWAWBXGWCAVPRSVSVT $.
    $( [4-Oct-2014] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Alternating congruential equations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( [JonesMatijasevic] uses "a \equiv \pm b (mod c)" for this construction.  The disjunction of divisibility constraints seems to adequately capture the concept, but it's rather verbose and somewhat inelegant $)

  $( A wff like that in this theorem will be known as an "alternating
     congruence".  A special symbol might be considered if more uses come up.
     They have many of the same properties as normal congruences, starting with
     reflexivity. $)
  acongid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A || ( B - B ) \/ A || ( B - -u B
      ) ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg congid orcd ) ACDBCDEABBFGHIABBJFGHI
    ABKL $.
    $( [2-Oct-2014] $)

  $( Symmetry of alternating congruence. $)
  acongsym $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\
          ( A || ( B - C ) \/ A || ( B - -u C ) ) ) -> ( A || ( C - B ) \/ A ||
      ( C - -u B ) ) ) $=
    ( cz wcel w3a cmin co cdivides wbr cneg wo wi congsym wceq zcn 3ad2ant2 syl
    wa cc exp32 3impia negneg oveq1d negcl neg2sub syl2anc eqtr3d breq2d biimpd
    3ad2ant3 orim12d imp ) ADEZBDEZCDEZFZABCGHIJZABCKZGHZIJZLACBGHIJZACBKZGHZIJ
    ZLUQURVBVAVEUNUOUPURVBMUNUOSUPURVBABCNUAUBUQVAVEUQUTVDAIUQVCKZUSGHZUTVDUQVF
    BUSGUQBTEZVFBOUOUNVHUPBPZQBUCRUDUQVCTEZCTEZVGVDOUOUNVJUPUOVHVJVIBUERQUPUNVK
    UOCPUKVCCUFUGUHUIUJULUM $.
    $( [2-Oct-2014] $)

  $( Negate right side of alternating congruence.  Makes essential use of the
     "alternating" part. $)
  acongneg2 $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\
          ( A || ( B - -u C ) \/ A || ( B - -u -u C ) ) ) -> ( A || ( B - C )
      \/ A || ( B - -u C ) ) ) $=
    ( cz wcel w3a cneg cmin co cdivides wbr wo wa cc zcn 3ad2ant3 negneg oveq2d
    wceq syl breq2d biimpd orim2d imp orcomd ) ADEZBDEZCDEZFZABCGZHIJKZABUJGZHI
    ZJKZLZMUKABCHIZJKZUIUOUKUQLUIUNUQUKUIUNUQUIUMUPAJUIULCBHUICNEZULCSUHUFURUGC
    OPCQTRUAUBUCUDUE $.
    $( [3-Oct-2014] $)

  $( Transitivity of alternating congruence. $)
  acongtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\
          ( ( A || ( B - C ) \/ A || ( B - -u C ) ) /\ ( A || ( C - D ) \/ A ||
      ( C - -u D ) ) ) ) -> ( A || ( B - D ) \/ A || ( B - -u D ) ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg wo congtr simpll ad2antlr simpr wceq
    ex adantl 3expa znegcl anim12i simplll simplrl simplrr congsym syl22anc zcn
    orcd cc adantr neg2sub syl2anc eqcomd breq2d sylibd anim2d imp syl3anc olcd
    anim2i anim1i simpl an42s syl12anc negneg syl oveq2d eqtr3d ccased 3impia )
    AEFZBEFZGZCEFZDEFZGZABCHIJKZABCLZHIJKZMACDHIJKZACDLZHIJKZMGABDHIJKZABWCHIJK
    ZMZVOVRGZVSWBWAWDWGWHVSWBGZWGWHWIGWEWFVOVRWIWEABCDNUAUJSWHWAWBGZWGWHWJGZWFW
    EWKVOVTEFZWCEFZGZWAAVTWCHIZJKZGZWFVOVRWJOVRWNVOWJVPWLVQWMCUBZDUBZUCZPWHWJWQ
    WHWBWPWAWHWBADCHIZJKZWPWHWBXBWHWBGVMVPVQWBXBVMVNVRWBUDVOVPVQWBUEVOVPVQWBUFW
    HWBQACDUGUHSWHXAWOAJWHWOXAVRWOXARZVOVRCUKFZDUKFZXCVPXDVQCUIULZVQXEVPDUITZCD
    UMUNTUOUPUQURUSABVTWCNUTVASWHVSWDGZWGWHXHGZWFWEXIVOVPWMGZXHWFVOVRXHOVRXJVOX
    HVQWMVPWSVBPWHXHQABCWCNUTVASWHWAWDGZWGWHXKGZWEWFXLVOWLVQGZWAAVTDHIZJKZGZWEV
    OVRXKOVRXMVOXKVPWLVQWRVCPWHXKXPWHWDXOWAWHWDAWCCHIZJKZXOWHWDXRWHWDGVMVPGZWMW
    DXRWHXSWDVMVQVNVPXSVMVQGVMVNVPGVPVMVQVDVNVPQUCVEULVRWMVOWDVQWMVPWSTPWHWDQAC
    WCUGVFSWHXQXNAJVRXQXNRVOVRWCVTLZHIZXQXNVRXTCWCHVRXDXTCRXFCVGVHVIVRXEVTUKFZY
    AXNRXGVRWNYBWTWLYBWMVTUIULVHDVTUMUNVJTUPUQURUSABVTDNUTUJSVKVL $.
    $( [2-Oct-2014] $)

  ${
    acongeq12d.1 $e |- ( ph -> B = C ) $.
    acongeq12d.2 $e |- ( ph -> D = E ) $.
    $( Substitution deduction for alternating congruence. $)
    acongeq12d $p |- ( ph -> ( ( A || ( B - D ) \/ A || ( B - -u D ) ) <-> ( A
        || ( C - E ) \/ A || ( C - -u E ) ) ) ) $=
      ( cmin co cdivides wbr cneg oveq12d breq2d negeqd orbi12d ) ABCEIJZKLBDFI
      JZKLBCEMZIJZKLBDFMZIJZKLARSBKACDEFIGHNOAUAUCBKACDTUBIGAEFHPNOQ $.
      $( [3-Oct-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.
    $( Every integer is alternating-congruent to some number in the first half
       of the fundamental domain. $)
    acongrep $p |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... A ) ( ( 2 x. A )
        || ( a - N ) \/ ( 2 x. A ) || ( a - -u N ) ) ) $=
      ( vb wcel cz wa c2 cmin cdivides wbr cc0 sylancr syl2anc cle syl3anc wceq
      co wb cc cn cmul cv c1 cfz wrex cneg wo 2nn simpl nnmulcl congrep elfzelz
      simpr cr zre syl ad2antrl nnre ad2antrr elfzle1 anim1i 0z a1i elfz adantr
      nnz mpbird simplrr orcd weq id acongeq12d rcla4ev simplll simplrl w3a clt
      eqidd elfzel1 3ad2ant2 2z zmulcl 3ad2ant1 simp2 biimpa syl21anc simp3d wi
      elfzm11 2re remulcl ltle mpd subge0 nncn caddc 2times oveq1d pncan2 eqtrd
      anidms simp3 eqbrtrd suble mpbid jca zsubcl simplr simprr congsym dvdsadd
      syl22anc zsscn sseldi zcn ad2antlr subneg recnd subadd23 breqtrrd lecasei
      olcd exp32 rexlimdv ) AUAEZBFEZGZHAUBRZDUCZBIRJKZDLYIUDIRZUERZUFZYICUCZBI
      RJKYIYOBUGZIRJKUHZCLAUERZUFZYHYIUAEZYGYNYHHUAEYFYTUIYFYGUJHAUKMYFYGUNYIBD
      ULNYHYKYSDYMYHYJYMEZYKYSYHUUAYKGZGZYSYJAUUAYJUOEZYHYKUUAYJFEZUUDYJLYLUMZY
      JUPUQZURZYFAUOEZYGUUBAUSZUTUUCYJAOKZGZYJYREZYKYIYJYPIRJKZUHZYSUULUUMLYJOK
      ZUUKGZUUCUUPUUKUUAUUPYHYKYJLYLVAURVBUUCUUMUUQSZUUKUUCUUELFEZAFEZUURUUAUUE
      YHYKUUFURZUUSUUCVCVDZYFUUTYGUUBAVGZUTZYJLAVEPVFVHUULYKUUNYHUUAYKUUKVIVJYQ
      UUOCYJYRCDVKZYIYOYJBBUVEVLUVEBVSVMVNNUUCAYJOKZGZYIYJIRZYREZYIUVHBIRJKZYIU
      VHYPIRZJKZUHZYSUVGUVILUVHOKZUVHAOKZGZUVGYFUUAUVFUVPYFYGUUBUVFVOYHUUAYKUVF
      VPUUCUVFUNYFUUAUVFVQZUVNUVOUVQUVNYJYIOKZUVQYJYIVRKZUVRUVQUUEUUPUVSUVQUUSY
      IFEZUUAUUEUUPUVSVQZUUAYFUUSUVFYJLYLVTWAYFUUAUVTUVFYFHFEZUUTUVTWBUVCHAWCZM
      WDYFUUAUVFWEUUSUVTGUUAUWAYJLYIWJWFWGWHUVQUUDYIUOEZUVSUVRWIUUAYFUUDUVFUUGW
      AZYFUUAUWDUVFYFHUOEUUIUWDWKUUJHAWLMWDZYJYIWMNWNUVQUWDUUDUVNUVRSUWFUWEYIYJ
      WONVHUVQYIAIRZYJOKZUVOUVQUWGAYJOYFUUAUWGAQZUVFYFATEZUWIAWPUWJUWGAAWQRZAIR
      ZAUWJYIUWKAIAWRWSUWJUWLAQAAWTXBXAUQWDYFUUAUVFXCXDUVQUWDUUIUUDUWHUVOSUWFYF
      UUAUUIUVFUUJWDUWEYIAYJXEPXFXGPUUCUVIUVPSZUVFUUCUVHFEZUUSUUTUWMUUCUVTUUEUW
      NUUCUWBUUTUVTWBUVDUWCMZUVAYIYJXHNZUVBUVDUVHLAVEPVFVHUVGUVLUVJUUCUVLUVFUUC
      YIYIBYJIRZWQRZUVKJUUCYIUWQJKZYIUWRJKZUUCUVTUUEYGYKUWSUWOUVAYFYGUUBXIZYHUU
      AYKXJYIYJBXKXMUUCUVTUWQFEZUWSUWTSUWOUUCYGUUEUXBUXAUVABYJXHNYIUWQXLNXFUUCU
      VKUVHBWQRZUWRUUCUVHTEBTEZUVKUXCQUUCFTUVHXNUWPXOYGUXDYFUUBBXPXQZUVHBXRNUUC
      YITEYJTEUXDUXCUWRQUUCFTYIXNUWOXOUUCYJUUHXSUXEYIYJBXTPXAYAVFYCYQUVMCUVHYRY
      OUVHQZYIYOUVHBBUXFVLUXFBVSVMVNNYBYDYEWN $.
      $( [2-Oct-2014] $)
  $}

  $( Bound on the difference between two integers constrained to two possibly
     overlapping finite ranges. $)
  fzmaxdif $p |- ( ( ( C e. ZZ /\ A e. ( B ... C ) ) /\ ( F e. ZZ /\ D e. ( E
      ... F ) ) /\ ( C - E ) <_ ( F - B ) ) -> ( abs ` ( A - D ) ) <_ ( F - B )
      ) $=
    ( cz wcel co cmin cle wbr cr wb zre 3syl syl resubcl syl2anc syl3anc cfz wa
    w3a cabs caddc simp1r elfzelz simp2r simp2l elfzel1 absdifle elfzle2 lesub1
    mpbid cc wceq recnd nncan breqtrd elfzle1 letrd simp1l readdcl lesub2 simp3
    cfv lesubadd addcom mpbir2and ) CGHZABCUAIHZUBZFGHZDEFUAIHZUBZCEJIZFBJIZKLZ
    UCZADJIUDVFVQKLZDVQJIZAKLZADVQUEIZKLZVSAMHZDMHZVQMHZVTWBWDUBNVSVKAGHWEVJVKV
    OVRUFZABCUGAOPZVSVNDGHWFVLVMVNVRUHZDEFUGDOPZVSFMHZBMHZWGVSVMWLVLVMVNVRUIFOQ
    ZVSVKBGHWMWHABCUJBOPZFBRSZADVQUKTVSWABAVSWFWGWAMHWKWPDVQRSWOWIVSWAFVQJIZBKV
    SDFKLZWAWQKLZVSVNWRWJDEFULQVSWFWLWGWRWSNWKWNWPDFVQUMTUNVSFUOHBUOHWQBUPVSFWN
    UQVSBWOUQFBURSUSVSVKBAKLWHABCUTQVAVSACWCWIVSVJCMHZVJVKVOVRVBCOQZVSWFWGWCMHW
    KWPDVQVCSVSVKACKLWHABCULQVSCVQDUEIZWCKVSCDJIZVQKLZCXBKLZVSXCVPVQVSWTWFXCMHX
    AWKCDRSVSWTEMHZVPMHXAVSVNEGHXFWJDEFUJEOPZCERSWPVSEDKLZXCVPKLZVSVNXHWJDEFUTQ
    VSXFWFWTXHXINXGWKXAEDCVDTUNVLVOVRVEVAVSWTWFWGXDXENXAWKWPCDVQVGTUNVSVQUOHDUO
    HXBWCUPVSVQWPUQVSDWKUQVQDVHSUSVAVI $.
    $( [4-Oct-2014] $)

  $( Reflection of a finite range of integers about 0. $)
  fzneg $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A e. ( B ... C ) <-> -u
      A e. ( -u C ... -u B ) ) ) $=
    ( cz wcel w3a cle wbr wa cneg cfz co ancom cr zre leneg syl2anc elfz znegcl
    wb 3ad2ant1 3ad2ant3 3ad2ant2 anbi12d syl5bb syl3an 3com23 3bitr4d ) ADEZBD
    EZCDEZFZBAGHZACGHZIZCJZAJZGHZUQBJZGHZIZABCKLEUQUPUSKLEZUOUNUMIULVAUMUNMULUN
    URUMUTULANEZCNEZUNURTUIUJVCUKAOUAZUKUIVDUJCOUBACPQULBNEZVCUMUTTUJUIVFUKBOUC
    VEBAPQUDUEABCRUIUKUJVBVATZUIUQDEUKUPDEUJUSDEVGASCSBSUQUPUSRUFUGUH $.
    $( [4-Oct-2014] $)

  $( Two numbers in the fundamental domain are alternating-congruent iff they
     are equal.  TODO: could be used to shorten ~ jm2.26 $)
  acongeq $p |- ( ( A e. NN /\ B e. ( 0 ... A ) /\ C e. ( 0 ... A ) ) -> ( B =
      C <-> ( ( 2 x. A ) || ( B - C ) \/ ( 2 x. A ) || ( B - -u C ) ) ) ) $=
    ( wcel cc0 co wceq c2 cmin wbr cz syl2anc clt cc cr syl cle caddc ad2antrr
    c1 cn cfz w3a cmul cdivides cneg wo wa nnz 3ad2ant1 zmulcl sylancr 3ad2ant2
    2z elfzelz congid adantr oveq2 adantl breqtrd orcd cabs cfv 3ad2ant3 zsubcl
    zsscn sseldi abscl nnre 0re resubcl sylancl 2re remulcl simp2 leid fzmaxdif
    simp3 syl221anc crp nnrp ltaddrp recnd subid1 2times 3brtr4d lelttrd wb 2nn
    simpl1 nnmulcl simpl2 simpl3 simpr congabseq syl31anc mpbid cuz nnnn0 nn0uz
    cn0 syl6eleq fzm1 biimpa renegcl recn 3syl 1re znegcl abssub elfzel1 0z a1i
    zssre 1z fzneg syl3anc neg0 oveq2d eleqtrd simpll2 simp1 nnm1nn0 nn0ge0 0cn
    subid1i ax-1cn addsubass oveq1d subneg 3eqtr4rd eqbrtrd ltm1 simplr elfzle1
    subcl zre mpbird eqtr4d jaodan letri3 le0neg1 negeqd 3eqtrd fveq2d eqbrtrrd
    mpbir2and ppncan addcom eqtrd 3eqtr4d breqtrrd dvdsadd mpdan impbida ) AUAD
    ZBEAUBFZDZCUUQDZUCZBCGZHAUDFZBCIFZUEJZUVBBCUFZIFZUEJZUGUUTUVAUHZUVDUVGUVHUV
    BBBIFZUVCUEUUTUVBUVIUEJZUVAUUTUVBKDZBKDZUVJUUTHKDAKDZUVKUNUUPUURUVMUUSAUIUJ
    ZHAUKULZUURUUPUVLUUSBEAUOZUMZUVBBUPLUQUVAUVIUVCGUUTBCBIURUSUTVAUUTUVDUVAUVG
    UUTUVDUHZUVCVBVCZUVBMJZUVAUUTUVTUVDUUTUVSAEIFZUVBUUTUVCNDUVSODUUTKNUVCVFUUT
    UVLCKDZUVCKDUVQUUSUUPUWBUURCEAUOZVDZBCVELVGUVCVHPUUTAODZEODZUWAODZUUPUURUWE
    UUSAVIUJZVJAEVKVLZUUTHODUWEUVBODZVMUWHHAVNULZUUTUVMUURUVMUUSUWAUWAQJZUVSUWA
    QJUVNUUPUURUUSVOUVNUUPUURUUSVRZUUTUWGUWLUWIUWAVPPBEACEAVQVSUUTAAARFZUWAUVBM
    UUTUWEAVTDZAUWNMJUWHUUPUURUWOUUSAWAUJAAWBLUUTANDZUWAAGUUTAUWHWCZAWDPUUTUWPU
    VBUWNGUWQAWEPZWFWGZUQUVRUVBUADZUVLUWBUVDUVTUVAWHUVRHUADZUUPUWTWIUUPUURUUSUV
    DWJHAWKZULUVRUURUVLUUPUURUUSUVDWLUVPPUVRUUSUWBUUPUURUUSUVDWMUWCPUUTUVDWNUVB
    BCWOWPWQUUTUVGUHZCEATIFZUBFDZCAGZUGZUVAUUTUXGUVGUUTAEWRVCZDZUUSUXGUUTAXAUXH
    UUPUURAXADUUSAWSUJWTXBUWMUXIUUSUXGCEAXCXDLUQUXCUXEUVAUXFUXCUXEUHZBECUXJBUVE
    EUFZEUXJUVFVBVCZUVBMJZBUVEGZUXJUXLAUXDUFZIFZUVBUUTUXLODZUVGUXEUUTUVFODZUVFN
    DUXQUUTBODUVEODZUXRUUTKOBXNUVQVGZUUTCODZUXSUUTKOCXNUWDVGZCXEPBUVEVKLUVFXFUV
    FVHXGSUUTUXPODZUVGUXEUUTUWEUXOODZUYCUWHUUTUXDODZUYDUUTUWETODUYEUWHXHATVKVLU
    XDXEPAUXOVKLSUUTUWJUVGUXEUWKSUXJUXLUVEBIFVBVCZUXPQUXJBNDZUVENDUXLUYFGUXJKNB
    VFUUTUVLUVGUXEUVQSZVGUXJKNUVEVFUUTUVEKDZUVGUXEUUTUUSUWBUYIUWMUWCCXIXGSZVGBU
    VEXJLUXJEKDZUVEUXOEUBFZDUVMUUREEIFZUXPQJZUYFUXPQJUXEUYKUXCCEUXDXKUSUXJUVEUX
    OUXKUBFZUYLUXJUXEUVEUYODZUXCUXEWNUUTUXEUYPWHZUVGUXEUUTUWBUYKUXDKDZUYQUWDUYK
    UUTXLXMUUTUVMTKDUYRUVNXOATVEVLCEUXDXPXQSWQUXJUXKEUXOUBUXKEGUXJXRXMZXSXTUUTU
    VMUVGUXEUVNSUUPUURUUSUVGUXEYAZUUTUYNUVGUXEUUTEUVBTIFZUYMUXPQUUTUWTVUAXADEVU
    AQJUUTUXAUUPUWTWIUUPUURUUSYBUXBULZUVBYCVUAYDXGUYMEGUUTEYEYFXMUUTUWNTIFZAUXD
    RFZVUAUXPUUTUWPUWPTNDZVUCVUDGUWQUWQVUEUUTYGXMAATYHXQUUTUVBUWNTIUWRYIUUTUWPU
    XDNDZUXPVUDGUWQUUTUWPVUEVUFUWQYGATYPVLAUXDYJLYKZWFSUVEUXOEBEAVQVSYLUUTUXPUV
    BMJUVGUXEUUTUXPVUAUVBMVUGUUTUWJVUAUVBMJUWKUVBYMPYLSWGUXJUWTUVLUYIUVGUXMUXNW
    HUUTUWTUVGUXEVUBSUYHUYJUUTUVGUXEYNUVBBUVEWOWPWQZUXJCEUXJCEGZCEQJZECQJZUXJUY
    AUWFVUIVUJVUKUHWHUXEUYAUXCUXEUWBUYACEUXDUOCYQPUSZVJCEUUAVLUXJVUJEUVEQJZUXJE
    BUVEQUXJUUREBQJUYTBEAYOPVUHUTUXJUYAVUJVUMWHVULCUUBPYRUXEVUKUXCCEUXDYOUSUUGZ
    UUCUYSUUDVUNYSUXCUXFUHZBACVUOBAIFZVBVCZUVBMJZBAGZVUOUVSVUQUVBMVUOUVCVUPVBUX
    FUVCVUPGUXCCABIURUSUUEUUTUVTUVGUXFUWSSUUFVUOUWTUVLUVMUVBVUPUEJZVURVUSWHUUTU
    WTUVGUXFVUBSUUTUVLUVGUXFUVQSUUTUVMUVGUXFUVNSVUOVUTUVBUVBVUPRFZUEJZVUOUVBUVF
    VVAUEUUTUVGUXFYNVUOUWNVUPRFZBCRFZVVAUVFVUOVVCBARFZVVDUUTVVCVVEGUVGUXFUUTVVC
    ABRFZVVEUUTUWPUWPUYGVVCVVFGUWQUWQUUTBUXTWCZAABUUHXQUUTUWPUYGVVFVVEGUWQVVGAB
    UUILUUJSUXFVVDVVEGUXCCABRURUSYSUUTVVAVVCGUVGUXFUUTUVBUWNVUPRUWRYISUUTUVFVVD
    GZUVGUXFUUTUYGCNDVVHVVGUUTCUYBWCBCYJLSUUKUULVUOUVKVUPKDZVUTVVBWHUUTUVKUVGUX
    FUVOSUUTVVIUVGUXFUUTUVLUVMVVIUVQUVNBAVELSUVBVUPUUMLYRUVBBAWOWPWQUXCUXFWNYSY
    TUUNYTUUO $.
    $( [4-Oct-2014] $)

  $( Alternating congruence passes from a base to a dividing base. $)
  dvdsacongtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( D
      || A /\ ( A || ( B - C ) \/ A || ( B - -u C ) ) ) ) -> ( D || ( B - C )
      \/ D || ( B - -u C ) ) ) $=
    ( cz wcel wa cdivides wbr cmin co wo simplr simpr wi ad2antrr zsubcl dvdstr
    syl2anc syl3anc cneg simprr simpll simprl mp2and znegcl syl orim12d expimpd
    ex 3impia ) AEFZBEFZGZCEFZDEFZGZDAHIZABCJKZHIZABCUAZJKZHIZLZGDUSHIZDVBHIZLZ
    UNUQGZURVDVGVHURGZUTVEVCVFVIUTVEVIUTGZURUTVEVHURUTMVIUTNVJUPULUSEFZURUTGVEO
    VHUPURUTUNUOUPUBZPVHULURUTULUMUQUCZPVJUMUOVKVHUMURUTULUMUQMZPVHUOURUTUNUOUP
    UDZPBCQSDAUSRTUEUJVIVCVFVIVCGZURVCVFVHURVCMVIVCNVPUPULVBEFZURVCGVFOVHUPURVC
    VLPVHULURVCVMPVPUMVAEFZVQVHUMURVCVNPVPUOVRVHUOURVCVOPCUFUGBVAQSDAVBRTUEUJUH
    UIUK $.
    $( [4-Oct-2014] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Additional theorems on integer divisibility
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Partial converse to ~ bezout .  Existance of a linear combination does not
     set the GCD, but it does upper bound it. $)
  bezoutr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( X e. ZZ /\ Y e. ZZ ) ) -> ( A
      gcd B ) || ( ( A x. X ) + ( B x. Y ) ) ) $=
    ( cz wcel wa cgcd co cmul cdivides wbr adantr zmulcl syl2anc w3a dvdsmultr1
    caddc imp syl31anc cn0 gcdcl syl simpll simprl simplr simprr gcddvds simpld
    nn0z simprd dvds2add syl32anc ) AEFZBEFZGZCEFZDEFZGZGZABHIZEFZACJIZEFZBDJIZ
    EFZVAVCKLZVAVEKLZVAVCVERIKLZUPVBUSUPVAUAFVBABUBVAUJUCMZUTUNUQVDUNUOUSUDZUPU
    QURUEZACNOUTUOURVFUNUOUSUFZUPUQURUGZBDNOUTVBUNUQVAAKLZVGVJVKVLUTVOVABKLZUPV
    OVPGUSABUHMZUIVBUNUQPVOVGVAACQSTUTVBUOURVPVHVJVMVNUTVOVPVQUKVBUOURPVPVHVABD
    QSTVBVDVFPVGVHGVIVAVCVEULSUM $.
    $( [23-Sep-2014] $)


  $( Converse of ~ bezout for the gcd = 1 case, sufficient condition for
     relative primality. $)
  bezoutr1 $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( X e. ZZ /\ Y e. ZZ ) ) -> ( (
      ( A x. X ) + ( B x. Y ) ) = 1 -> ( A gcd B ) = 1 ) ) $=
    ( cz wcel wa cmul co caddc c1 wceq wbr cdivides cn syl a1i syl2anc cc0 wne
    cgcd cle bezoutr adantr simpr breqtrd wi cn0 gcdcl nn0z ad2antrr 1nn dvdsle
    mpd wb wn simpll oveq1 oveqan12d cc zcn mul02 sylan9eqr 00id syl6eq adantll
    ax-1ne0 necomi eqnetrd ex necon2bd imp gcdn0cl nnle1eq1 mpbid ) AEFBEFGZCEF
    ZDEFZGZGZACHIZBDHIZJIZKLZABUAIZKLZVTWDGZWEKUBMZWFWGWEKNMZWHWGWEWCKNVTWEWCNM
    WDABCDUCUDVTWDUEUFWGWEEFZKOFZWIWHUGVPWJVSWDVPWEUHFWJABUIWEUJPUKWKWGULQWEKUM
    RUNWGWEOFZWHWFUOWGVPASLZBSLZGZUPZWLVPVSWDUQVTWDWPVTWOWCKVTWOWCKTVTWOGZWCSKV
    SWOWCSLVPVSWOGWCSSJIZSWOVSWCSCHIZSDHIZJIWRWMWNWAWSWBWTJASCHURBSDHURUSVQVRWS
    SWTSJVQCUTFWSSLCVACVBPVRDUTFWTSLDVADVBPUSVCVDVEVFSKTWQKSVGVHQVIVJVKVLABVMRW
    EVNPVOVJ $.
    $( [23-Sep-2014] $)

  $( Adding a multiple of the base does not affect divisibility. $)
  dvdsadd2b $p |- ( ( A e. ZZ /\ B e. ZZ /\ ( C e. ZZ /\ A || C ) ) -> ( A || B
      <-> A || ( C + B ) ) ) $=
    ( cz wcel cdivides wbr wa w3a caddc co simpl1 simpl3l simpl2 simpl3r adantr
    syl2anc wceq cc zcn simpr dvds2add syl32anc cneg simp3l simp2 zaddcl znegcl
    imp syl wb dvdsnegb mpbid ancoms adantl negsub pncan2 eqtrd breqtrd impbida
    cmin ) ADEZBDEZCDEZACFGZHZIZABFGZACBJKZFGZVGVHHVBVDVCVEVHVJVBVCVFVHLVDVEVBV
    CVHMVBVCVFVHNVDVEVBVCVHOVGVHUAVBVDVCIVEVHHVJACBUBUIUCVGVJHZAVICUDZJKZBFVKVB
    VIDEZVLDEZVJAVLFGZAVMFGZVBVCVFVJLZVGVNVJVGVDVCVNVBVCVDVEUEZVBVCVFUFCBUGZQPV
    GVOVJVGVDVOVSCUHUJPVGVJUAVKVEVPVDVEVBVCVJOVKVBVDVEVPUKVRVDVEVBVCVJMZACULQUM
    VBVNVOIVJVPHVQAVIVLUBUIUCVKVCVDVMBRVBVCVFVJNWAVCVDHZVMVICVAKZBWBVISEZCSEZVM
    WCRWBVNWDVDVCVNVTUNVITUJVDWEVCCTUOZVICUPQWBWEBSEZWCBRWFVCWGVDBTPCBUQQURQUSU
    T $.
    $( [23-Sep-2014] $)

  $( Multiplication by a coprime number does not affect divisibility. $)
  coprmdvdsb $p |- ( ( K e. ZZ /\ N e. ZZ /\ ( M e. ZZ /\ ( K gcd M ) = 1 ) )
      -> ( K || N <-> K || ( M x. N ) ) ) $=
    ( cz wcel cgcd co c1 wceq wa w3a cdivides wbr simp1 simp3l simp2 dvdsmultr2
    cmul wi syl3anc simp3r coprmdvds mpan2d impbid ) ADEZCDEZBDEZABFGHIZJZKZACL
    MZABCRGLMZUJUEUGUFUKULSUEUFUINZUEUFUGUHOZUEUFUIPZABCQTUJULUHUKUEUFUGUHUAUJU
    EUGUFULUHJUKSUMUNUOABCUBTUCUD $.
    $( [23-Sep-2014] $)

  $( The absolute value of an integer is an integer. $)
  zabscl $p |- ( A e. ZZ -> ( abs ` A ) e. ZZ ) $=
    ( cz wcel cabs cfv cn0 nn0abscl nn0z syl ) ABCADEZFCJBCAGJHI $.
    $( [24-Sep-2014] $)

  $( The square of a natural number is a natural number. $)
  nn0sqcl $p |- ( A e. NN0 -> ( A ^ 2 ) e. NN0 ) $=
    ( cn0 wcel c2 cexp co 2nn0 nn0expcl mpan2 ) ABCDBCADEFBCGADHI $.
    $( [16-Oct-2014] $)

  $( Transfer divisibility to an order constraint on absolute values. $)
  dvdsleabs2 $p |- ( ( M e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( M || N -> ( abs ` M
      ) <_ ( abs ` N ) ) ) $=
    ( cz wcel cc0 wne w3a cdivides wbr cabs cfv cle wa zabscl 3anim1i adantr wb
    absdvdsb 3adant3 biimpa dvdsleabs sylc ex ) ACDZBCDZBEFZGZABHIZAJKZBJKLIZUG
    UHMUICDZUEUFGZUIBHIZUJUGULUHUDUKUEUFANOPUGUHUMUDUEUHUMQUFABRSTUIBUAUBUC $.
    $( [24-Sep-2014] $)

  $( Divisibility in terms of modular reduction by the absolute value of the
     base. $)
  modabsdifz $p |- ( ( N e. RR /\ M e. RR /\ M =/= 0 ) -> ( ( N - ( N mod ( abs
      ` M ) ) ) / M ) e. ZZ ) $=
    ( cr wcel cc0 wne cabs cfv co cdiv cz recnd syl2anc wceq syl absdiv syl3anc
    cc wb redivcl w3a cmo simp1 simp2 simp3 absrpcl moddifz absidm oveq2d modcl
    cmin crp resubcl rpre rpne0 3eqtr4d eleq1d absz 3bitr4d mpbid ) BCDZACDZAEF
    ZUAZBBAGHZUBIZUKIZVEJIZKDZVGAJIZKDZVDVAVEULDZVIVAVBVCUCZVDARDZVCVLVDAVAVBVC
    UDZLZVAVBVCUEZAUFMZBVEUGMVDVHGHZKDZVJGHZKDZVIVKVDVSWAKVDVGGHZVEGHZJIZWCVEJI
    ZVSWAVDWDVEWCJVDVNWDVENVPAUHOUIVDVGRDZVERDVEEFZVSWENVDVGVDVAVFCDZVGCDZVMVDV
    AVLWIVMVRBVEUJMBVFUMMZLZVDVEVDVLVECDZVRVEUNOZLVDVLWHVRVEUOOZVGVEPQVDWGVNVCW
    AWFNWLVPVQVGAPQUPUQVDVHCDZVIVTSVDWJWMWHWPWKWNWOVGVETQVHUROVDVJCDZVKWBSVDWJV
    BVCWQWKVOVQVGATQVJUROUSUT $.
    $( [26-Sep-2014] $)

  $( Divisibility in terms of modular reduction by the absolute value of the
     base. $)
  dvdsabsmod0 $p |- ( ( M e. ZZ /\ N e. ZZ /\ M =/= 0 ) -> ( M || N <-> ( N mod
      ( abs ` M ) ) = 0 ) ) $=
    ( cz wcel cc0 wne w3a cdivides wbr cabs cfv cmin co cmo wb absdvdsb 3adant3
    wceq cc zcn 3ad2ant2 subid1 syl breq2d bitr4d nnabscl 3adant2 simp2 moddvds
    cn 0z a1i syl3anc crp nnrp 0mod 3syl eqeq2d 3bitr2d ) ACDZBCDZAEFZGZABHIZAJ
    KZBELMZHIZBVENMZEVENMZRZVHERVCVDVEBHIZVGUTVAVDVKOVBABPQVCVFBVEHVCBSDZVFBRVA
    UTVLVBBTUABUBUCUDUEVCVEUJDZVAECDZVJVGOUTVBVMVAAUFUGZUTVAVBUHVNVCUKULBEVEUIU
    MVCVIEVHVCVMVEUNDVIERVOVEUOVEUPUQURUS $.
    $( [24-Sep-2014] $)

  $( Relative primality passes to asymmetric powers. $)
  rpexp1i $p |- ( ( A e. ZZ /\ B e. ZZ /\ M e. NN0 ) -> ( ( A gcd B ) = 1 -> (
      ( A ^ M ) gcd B ) = 1 ) ) $=
    ( cz wcel cn0 cgcd co c1 wceq cexp wi wa cn cc0 wo elnn0 w3a rpexp eqtrd cc
    biimprd 3expa simpr oveq2d zcn ad2antrr exp0 syl oveq1d ad2antlr a1d jaodan
    1gcd sylan2b 3impa ) ADEZBDEZCFEZABGHIJZACKHZBGHZIJZLZUSUQURMZCNEZCOJZPVDCQ
    VEVFVDVGUQURVFVDUQURVFRVCUTABCSUBUCVEVGMZVCUTVHVBIBGHZIVHVAIBGVHVAAOKHZIVHC
    OAKVEVGUDUEVHAUAEZVJIJUQVKURVGAUFUGAUHUITUJURVIIJUQVGBUNUKTULUMUOUP $.
    $( [27-Sep-2014] $)

  $( Relative primality passes to symmetric powers. $)
  rpexp12i $p |- ( ( A e. ZZ /\ B e. ZZ /\ ( M e. NN0 /\ N e. NN0 ) ) -> ( ( A
      gcd B ) = 1 -> ( ( A ^ M ) gcd ( B ^ N ) ) = 1 ) ) $=
    ( cz wcel cn0 wa w3a cgcd co wceq cexp rpexp1i zexpcl syl2anc gcdcom eqeq1d
    c1 wi 3adant3r simp2 simp1 simp3l simp3r syl3anc 3imtr4d syld ) AEFZBEFZCGF
    ZDGFZHZIZABJKSLZACMKZBJKZSLZUPBDMKZJKZSLZUIUJUKUOURTULABCNUAUNBUPJKZSLZUSUP
    JKZSLZURVAUNUJUPEFZULVCVETUIUJUMUBZUNUIUKVFUIUJUMUCUIUJUKULUDACOPZUIUJUKULU
    EZBUPDNUFUNUQVBSUNVFUJUQVBLVHVGUPBQPRUNUTVDSUNVFUSEFZUTVDLVHUNUJULVJVGVIBDO
    PUPUSQPRUGUH $.
    $( [27-Sep-2014] $)

  ${
    $d N a $.  $d D a $.  $d R a $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    divalgmodcl $p |- ( ( N e. ZZ /\ D e. NN /\ R e. NN0 ) ->
        ( R = ( N mod D ) <-> ( R < D /\ D || ( N - R ) ) ) ) $=
      ( va cz wcel cn cn0 cmo co wceq clt wbr cmin cdivides wa wb cv wi anbi12d
      eqeq1 eleq1 breq1 oveq2 breq2d imbi2d divalgmod vtoclg impcom ibar adantl
      bibi12d bitr4d 3impa ) CEFZAGFZBHFZBCAIJZKZBALMZACBNJZOMZPZQUOUPPZUQPUSUQ
      VCPZVCUQVDUSVEQZVDDRZURKZVGHFZVGALMZACVGNJZOMZPZPZQZSVDVFSDBHVGBKZVOVFVDV
      PVHUSVNVEVGBURUAVPVIUQVMVCVGBHUBVPVJUTVLVBVGBALUCVPVKVAAOVGBCNUDUETTULUFA
      CDUGUHUIUQVCVEQVDUQVCUJUKUMUN $.
      $( [17-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    X and Y sequences 3: Divisibility properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b $.  $d K a b $.  $d N a b $.
    $( Statement 2.18 of [JonesMatijasevic].  Direct relationship of the
       exponential function to X and Y sequences. $)
    jm2.18 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ K e. NN0 /\ N e. NN0 ) ->
        ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) - 1 ) ||
        ( ( ( A rmX N ) - ( ( A - K ) x. ( A rmY N ) ) ) - ( K ^ N ) ) ) $=
      ( wcel cmul co cexp cmin cdivides wbr cc0 adantr syl2anc syl wceq oveq12d
      c1 cz cc oveq2 va vb c2 cuz cfv cn0 crmx wa cv wi caddc 2z eluzelz zmulcl
      crmy sylancr nn0z adantl zsqcl zsubcl dvds0 rmx0 rmy0 oveq2d zsscn sseldi
      peano2zm mul01 eqtrd ax-1cn subid1i syl6eq exp0 subidi breqtrrd rmx1 rmy1
      nn0cn mulid1 nncan exp1 subid cn pm3.43 nn0ssz simpll nnz frmx fovcl frmy
      jca nnnn0 zexpcl nnm1nn0 0z zaddcl w3a 3jca ad2antrr congid simpr congmul
      syl112anc adantrl simprl congsub a1i iddvds subid1 congadd syl322anc sqcl
      addsub syl3anc npcan oveq1d eqtr3d expcl subdi mul12 expm1t eqtr4d congtr
      ad2antlr 3eqtrrd rmxluc rmyluc zcn subcl mulcl mulcom 3eqtrd nn0sscn sub4
      2cn syl22anc eqcomd expp1 breq2d imbi2d nncn sylancl mulass addid2 eqtr2d
      sqval ex expcom a2d syl5 weq 2nn0ind impcom 3impa ) AUCUDUEZDZBUFDZCUFDZU
      CAEFZBEFZBUCGFZHFZQHFZACUGFZABHFZACUOFZEFZHFZBCGFZHFZIJZUURUUPUUQUHZUVKUV
      LUVCAUAUIZUGFZUVEAUVMUOFZEFZHFZBUVMGFZHFZIJZUJUVLUVCAKUGFZUVEAKUOFZEFZHFZ
      BKGFZHFZIJZUJUVLUVCAQUGFZUVEAQUOFZEFZHFZBQGFZHFZIJZUJUVLUVCAUBUIZQHFZUGFZ
      UVEAUWPUOFZEFZHFZBUWPGFZHFZIJZUJZUVLUVCAUWOUGFZUVEAUWOUOFZEFZHFZBUWOGFZHF
      ZIJZUJZUVLUVCAUWOQUKFZUGFZUVEAUXMUOFZEFZHFZBUXMGFZHFZIJZUJZUVLUVKUJUAUBCU
      VLUVCKUWFIUVLUVCRDZUVCKIJUVLUVBRDZUYBUVLUUTRDZUVARDZUYCUVLUUSRDZBRDZUYDUV
      LUCRDARDZUYFULUUPUYHUUQUCAUMZLZUCAUNUPZUUQUYGUUPBUQURZUUSBUNMZUVLUYGUYEUY
      LBUSNZUUTUVAUTMZUVBVGNZUVCVANZUVLUWFQQHFKUVLUWDQUWEQHUVLUWDQKHFQUVLUWAQUW
      CKHUUPUWAQOUUQAVBLUVLUWCUVEKEFZKUVLUWBKUVEEUUPUWBKOUUQAVCLVDUVLUVESDZUYRK
      OUVLRSUVEVEUVLUYHUYGUVERDZUYJUYLABUTMZVFZUVEVHNVIPQVJVKVLUVLBSDZUWEQOUUQV
      UCUUPBVRZURZBVMNPQVJVNVLVOUVLUVCKUWMIUYQUVLUWMBBHFZKUVLUWKBUWLBHUVLUWKAUV
      EHFZBUVLUWHAUWJUVEHUUPUWHAOUUQAVPLUVLUWJUVEQEFZUVEUVLUWIQUVEEUUPUWIQOUUQA
      VQLVDUVLUYSVUHUVEOVUBUVEVSNVIPUVLASDZVUCVUGBOUVLRSAVEUYJVFVUEABVTMVIUVLVU
      CUWLBOVUEBWANPUVLVUCVUFKOVUEBWBNVIVOUXDUXLUHUVLUXCUXKUHZUJUWOWCDZUYAUVLUX
      CUXKWDVUKUVLVUJUXTUVLVUKVUJUXTUJUVLVUKUHZVUJUXTVULVUJUHZUVCUUSUXHEFZUWTHF
      ZUXAKUVAUKFZEFZHFZUXSIVUMUYBVUORDZUHZUUSUXIEFZUXAHFZRDZVUQRDZUHZUVCVUOVVB
      HFIJZUVCVVBVUQHFZIJZUVCVURIJVULVUTVUJVULUYBVUSUVLUYBVUKUYPLZVULVUNRDZUWTR
      DZVUSVULUYFUXHRDZVVJUVLUYFVUKUYKLZVULUXERDUXGRDZVVLVULUFRUXEWEVULUUPUWORD
      ZUXEUFDUUPUUQVUKWFZVUKVVOUVLUWOWGURZAUWOUFUUORUGWHWIZMVFVULUYTUXFRDZVVNUV
      LUYTVUKVUALZVULUUPVVOVVSVVPVVQAUWORUUORUOWJWIZMUVEUXFUNMUXEUXGUTMZUUSUXHU
      NMZVULUWQRDUWSRDZVVKVULUFRUWQWEVULUUPUWPRDZUWQUFDVVPVULVVOVWEVVQUWOVGNZAU
      WPUFUUORUGWHWIZMVFVULUYTUWRRDZVWDVVTVULUUPVWEVWHVVPVWFAUWPRUUORUOWJWIZMUV
      EUWRUNMUWQUWSUTMZVUNUWTUTMWKLVULVVEVUJVULVVCVVDVULVVARDZUXARDZVVCVULUYFUX
      IRDZVWKVVMVULUYGUWOUFDZVWMUVLUYGVUKUYLLZVUKVWNUVLUWOWLURZBUWOWMMZUUSUXIUN
      MZVULUYGUWPUFDZVWLVWOVUKVWSUVLUWOWNURZBUWPWMMZVVAUXAUTMVULVWLVUPRDZVVDVXA
      UVLVXBVUKUVLKRDZUYEVXBWOUYNKUVAWPUPLZUXAVUPUNMWKLVUMUYBVVJVWKWQZVVKVWLUHZ
      UVCVUNVVAHFIJZUXCVVFVULVXEVUJVULUYBVVJVWKVVIVWCVWRWRLVULVXFVUJVULVVKVWLVW
      JVXAWKLVULUXKVXGUXCVULUXKUHUYBUYFUYFWQZVVLVWMUHZUVCUUSUUSHFIJZUXKVXGUVLVX
      HVUKUXKUVLUYBUYFUYFUYPUYKUYKWRWSVULVXIUXKVULVVLVWMVWBVWQWKLUVLVXJVUKUXKUV
      LUYBUYFVXJUYPUYKUVCUUSWTMWSVULUXKXAUVCUUSUUSUXHUXIXBXCXDVULUXCUXKXEUVCVUN
      VVAUWTUXAXFXCVULVVHVUJVULUVCUXAUVCUVAUKFZEFZVUQHFZVVGIVULUYBVWLVWLVXKRDZV
      XBUVCUXAUXAHFIJZUVCVXKVUPHFIJZUVCVXMIJVVIVXAVXAUVLVXNVUKUVLUYBUYEVXNUYPUY
      NUVCUVAWPMLVXDVULUYBVWLVXOVVIVXAUVCUXAWTMUVLVXPVUKUVLUYBUYBVXCUYEUYEUVCUV
      CKHFZIJUVCUVAUVAHFIJZVXPUYPUYPVXCUVLWOXGUYNUYNUVLUVCUVCVXQIUVLUYBUVCUVCIJ
      UYPUVCXHNUVLUVCSDVXQUVCOUVLRSUVCVEUYPVFUVCXINVOUVLUYBUYEVXRUYPUYNUVCUVAWT
      MUVCUVCKUVAUVAXJXKLUVCUXAUXAVXKVUPXBXKVULVVBVXLVUQHVULVXLUXAUUTQHFZEFZUXA
      UUTEFZUXAQEFZHFZVVBVULVXKVXSUXAEUVLVXKVXSOVUKUVLUVBUVAUKFZQHFZVXKVXSUVLUV
      BSDUVASDZQSDZVYEVXKOUVLRSUVBVEUYOVFUVLVUCVYFVUEBXLNZVYGUVLVJXGUVBUVAQXMXN
      UVLVYDUUTQHUVLUUTSDZVYFVYDUUTOUVLRSUUTVEUYMVFZVYHUUTUVAXOMXPXQLVDVULUXASD
      ZVYIVYGVXTVYCOVULVUCVWSVYKUUQVUCUUPVUKVUDYDZVWTBUWPXRMZUVLVYIVUKVYJLVYGVU
      LVJXGUXAUUTQXSXNVULVYAVVAVYBUXAHVULVYAUUSUXABEFZEFZVVAVULVYKUUSSDZVUCVYAV
      YOOVYMUVLVYPVUKUVLRSUUSVEUYKVFLZVYLUXAUUSBXTXNVULUXIVYNUUSEVULVUCVUKUXIVY
      NOVYLUVLVUKXABUWOYAMVDYBVULVYKVYBUXAOVYMUXAVSNPYEXPVOLUVCVUOVVBVUQYCXCVUL
      UXSVUROVUJVULUXQVUOUXRVUQHVULUXQUUSUXEEFZUWQHFZUUSUXGEFZUWSHFZHFZVYRVYTHF
      ZUWTHFZVUOVULUXNVYSUXPWUAHVULUUPVVOUXNVYSOVVPVVQAUWOYFMVULUXPUVEUCUXFAEFZ
      EFZUWRHFZEFZUVEWUFEFZUWSHFZWUAVULUXOWUGUVEEVULUUPVVOUXOWUGOVVPVVQAUWOYGMV
      DVULUYSWUFSDZUWRSDZWUHWUJOVULVUIVUCUYSUUPVUIUUQVUKUUPUYHVUIUYIAYHNWSZVYLA
      BYIMZVULUCSDZWUESDZWUKYOVULUXFSDZVUIWUPVULUUPVVOWUQVVPVVQUUPVVOUHZRSUXFVE
      VWAVFMZWUMUXFAYJMUCWUEYJUPVULUUPVWEWULVVPVWFUUPVWEUHZRSUWRVEVWIVFMZUVEWUF
      UWRXSXNVULWUIVYTUWSHVULWUIUVEUUSUXFEFZEFZVYTVULWUFWVBUVEEVULWUFUXFUUSEFZW
      VBVULWUOWUQVUIWUFWVDOWUOVULYOXGWUSWUMUCUXFAXTXNVULWUQVYPWVDWVBOWUSVYQUXFU
      USYKMVIVDVULUYSVYPWUQWVCVYTOWUNVYQWUSUVEUUSUXFXTXNVIXPYLPVULVYRSDZUWQSDZV
      YTSDZUWSSDZWUBWUDOVULVYPUXESDZWVEVYQVULUUPVVOWVIVVPVVQWURUFSUXEYMVVRVFMZU
      USUXEYJMVULUUPVWEWVFVVPVWFWUTUFSUWQYMVWGVFMVULVYPUXGSDZWVGVYQVULUYSWUQWVK
      WUNWUSUVEUXFYJMZUUSUXGYJMVULUYSWULWVHWUNWVAUVEUWRYJMVYRUWQVYTUWSYNYPVULWU
      CVUNUWTHVULVUNWUCVULVYPWVIWVKVUNWUCOVYQWVJWVLUUSUXEUXGXSXNYQXPYLVULUXRUXI
      BEFZVYNBEFZVUQVULVUCVWNUXRWVMOVYLVWPBUWOYRMVULUXIVYNBEVULBUWPQUKFZGFZUXIV
      YNVULWVOUWOBGVULUWOSDZVYGWVOUWOOVUKWVQUVLUWOUUAURVJUWOQXOUUBVDVULVUCVWSWV
      PVYNOVYLVWTBUWPYRMXQXPVULWVNUXABBEFZEFZVUQVULVYKVUCVUCWVNWVSOVYMVYLVYLUXA
      BBUUCXNVULWVRVUPUXAEUVLWVRVUPOVUKUVLVUPUVAWVRUVLVYFVUPUVAOVYHUVAUUDNUVLVU
      CUVAWVROVUEBUUFNUUELVDVIYLPLVOUUGUUHUUIUUJUVMKOZUVTUWGUVLWVTUVSUWFUVCIWVT
      UVQUWDUVRUWEHWVTUVNUWAUVPUWCHUVMKAUGTWVTUVOUWBUVEEUVMKAUOTVDPUVMKBGTPYSYT
      UVMQOZUVTUWNUVLWWAUVSUWMUVCIWWAUVQUWKUVRUWLHWWAUVNUWHUVPUWJHUVMQAUGTWWAUV
      OUWIUVEEUVMQAUOTVDPUVMQBGTPYSYTUVMUWPOZUVTUXCUVLWWBUVSUXBUVCIWWBUVQUWTUVR
      UXAHWWBUVNUWQUVPUWSHUVMUWPAUGTWWBUVOUWRUVEEUVMUWPAUOTVDPUVMUWPBGTPYSYTUAU
      BUUKZUVTUXKUVLWWCUVSUXJUVCIWWCUVQUXHUVRUXIHWWCUVNUXEUVPUXGHUVMUWOAUGTWWCU
      VOUXFUVEEUVMUWOAUOTVDPUVMUWOBGTPYSYTUVMUXMOZUVTUXTUVLWWDUVSUXSUVCIWWDUVQU
      XQUVRUXRHWWDUVNUXNUVPUXPHUVMUXMAUGTWWDUVOUXOUVEEUVMUXMAUOTVDPUVMUXMBGTPYS
      YTUVMCOZUVTUVKUVLWWEUVSUVJUVCIWWEUVQUVHUVRUVIHWWEUVNUVDUVPUVGHUVMCAUGTWWE
      UVOUVFUVEEUVMCAUOTVDPUVMCBGTPYSYTUULUUMUUN $.
      $( [14-Oct-2014] $)
  $}

  $( Lemma for ~ jm2.29 .  X and Y values are coprime. $)
  jm2.19lem1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ ) -> ( ( A rmX M ) gcd ( A
      rmY M ) ) = 1 ) $=
    ( c2 wcel cz crmx co cmul crmy cexp c1 cmin cneg caddc wceq cn0 syl syl2anc
    cc cn cuz wa cgcd frmx fovcl nn0cn sqcl csquarenn rmspecnonsq eldifi adantr
    cfv cdif nncn frmy mulcl negsub sqval oveq2d mulneg1 nnnegz syl3anc 3eqtr3d
    zcn mul12 oveq12d rmxynorm wi nn0ssz sseldi zmulcl bezoutr1 syl22anc mpd )
    ACUAULZDZBEDZUBZABFGZVSHGZABIGZACJGKLGZMZWAHGZHGZNGZKOZVSWAUCGKOZVRVSCJGZWB
    WACJGZHGZMZNGZWIWKLGZWFKVRWISDZWKSDZWMWNOVRVSSDZWOVRVSPDWQABPVOEFUDUEZVSUFQ
    ZVSUGQVRWBSDZWJSDZWPVRWBTDZWTVPXBVQVPWBTUHUMDXBAUIWBTUHUJQUKZWBUNQZVRWASDZX
    AVRWAEDZXEABEVOEIUOUEZWAVDQZWAUGQZWBWJUPRWIWKUQRVRWIVTWLWENVRWQWIVTOWSVSURQ
    VRWCWJHGZWCWAWAHGZHGZWLWEVRWJXKWCHVRXEWJXKOXHWAURQUSVRWTXAXJWLOXDXIWBWJUTRV
    RWCSDZXEXEXLWEOVRWCEDZXMVRXBXNXCWBVAQZWCVDQXHXHWCWAWAVEVBVCVFABVGVCVRVSEDZX
    FXPWDEDZWGWHVHVRPEVSVIWRVJZXGXRVRXNXFXQXOXGWCWAVKRVSWAVSWDVLVMVN $.
    $( [23-Sep-2014] $)

  $( Lemma for ~ jm2.19 . $)
  jm2.19lem2 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( ( A rmY M
      ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + M ) ) ) ) $=
    ( wcel cz crmy co cdivides wbr crmx cmul caddc c1 wceq fovcl 3adant3 sseldi
    cn0 syl2anc cc c2 cuz cfv w3a cgcd wb frmy 3adant2 nn0ssz gcdcom jm2.19lem1
    frmx eqtrd coprmdvdsb syl112anc nn0sscn zsscn mulcom breq2d zmulcl dvdsmul2
    bitrd dvdsadd2b rmyadd 3com23 mulcl addcom eqtr2d 3bitrd ) AUAUBUCZDZBEDZCE
    DZUDZABFGZACFGZHIZVOVPABJGZKGZHIZVOACJGZVOKGZVSLGZHIZVOACBLGFGZHIVNVQVOVRVP
    KGZHIZVTVNVOEDZVPEDZVREDZVOVRUEGZMNVQWGUFVKVLWHVMABEVJEFUGOPZVKVMWIVLACEVJE
    FUGOUHZVNREVRUIVKVLVRRDVMABRVJEJULOPZQZVNWKVRVOUEGZMVNWHWJWKWPNWLWOVOVRUJSV
    KVLWPMNVMABUKPUMVOVRVPUNUOVNWFVSVOHVNVRTDZVPTDZWFVSNVNRTVRUPWNQZVNETVPUQWMQ
    ZVRVPURSUSVBVNWHVSEDZWBEDZVOWBHIZVTWDUFWLVNWIWJXAWMWOVPVRUTSVNWAEDZWHXBVNRE
    WAUIVKVMWARDVLACRVJEJULOUHQZWLWAVOUTSVNXDWHXCXEWLWAVOVASVOVSWBVCUOVNWCWEVOH
    VNWEVSWBLGZWCVKVMVLWEXFNACBVDVEVNVSTDZWBTDZXFWCNVNWRWQXGWTWSVPVRVFSVNWATDVO
    TDXHVNETWAUQXEQVNETVOUQWLQWAVOVFSVSWBVGSVHUSVI $.
    $( [23-Sep-2014] $)

  ${
    $d A a b $.  $d M a b $.  $d N a b $.  $d I a b $.
    $( Lemma for ~ jm2.19 . $)
    jm2.19lem3 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e.
        NN0 ) -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N +
        ( I x. M ) ) ) ) ) $=
      ( wcel cz crmy co cdivides wbr cmul caddc wb wi cc0 wceq oveq2d breq2d cc
      syl va vb c2 cuz cfv wa cn0 cv oveq1 bibi2d imbi2d weq zcn ad2antrl mul02
      c1 ad2antll addid1 eqtr2d simp3 simprl simprrl simprrr nn0z adantr zmulcl
      syl2anc zaddcl jm2.19lem2 syl3anc addass nn0cn ax-1cn adddir mulid2 eqtrd
      w3a a1i bitrd 3adant3 3exp a2d nn0ind com12 3impia ) AUCUDUEEZCFEZDFEZUFZ
      BUGEZACGHZADGHZIJZWKADBCKHZLHZGHZIJZMZWJWFWIUFZWRWSWMWKADUAUHZCKHZLHZGHZI
      JZMZNWSWMWKADOCKHZLHZGHZIJZMZNWSWMWKADUBUHZCKHZLHZGHZIJZMZNWSWMWKADXKUPLH
      ZCKHZLHZGHZIJZMZNWSWRNUAUBBWTOPZXEXJWSYCXDXIWMYCXCXHWKIYCXBXGAGYCXAXFDLWT
      OCKUIQQRUJUKUAUBULZXEXPWSYDXDXOWMYDXCXNWKIYDXBXMAGYDXAXLDLWTXKCKUIQQRUJUK
      WTXQPZXEYBWSYEXDYAWMYEXCXTWKIYEXBXSAGYEXAXRDLWTXQCKUIQQRUJUKWTBPZXEWRWSYF
      XDWQWMYFXCWPWKIYFXBWOAGYFXAWNDLWTBCKUIQQRUJUKWSWLXHWKIWSDXGAGWSXGDOLHZDWS
      XFODLWSCSEZXFOPWGYHWFWHCUMZUNCUOTQWSDSEZYGDPWHYJWFWGDUMZUQDURTUSQRXKUGEZW
      SXPYBYLWSXPYBYLWSXPVQWMXOYAYLWSXPUTYLWSXOYAMXPYLWSUFZXOWKAXMCLHZGHZIJZYAY
      MWFWGXMFEZXOYPMYLWFWIVAYLWFWGWHVBZYMWHXLFEZYQYLWFWGWHVCZYMXKFEZWGYSYLUUAW
      SXKVDVEYRXKCVFVGZDXLVHVGACXMVIVJYMYOXTWKIYMYNXSAGYMYNDXLCLHZLHZXSYMYJXLSE
      ZYHYNUUDPYMWHYJYTYKTYMYSUUEUUBXLUMTYMWGYHYRYITZDXLCVKVJYMUUCXRDLYMXRXLUPC
      KHZLHZUUCYMXKSEZUPSEZYHXRUUHPYLUUIWSXKVLVEUUJYMVMVRUUFXKUPCVNVJYMUUGCXLLY
      MYHUUGCPUUFCVOTQUSQVPQRVSVTVSWAWBWCWDWE $.
      $( [26-Sep-2014] $)
  $}

  $( Lemma for ~ jm2.19 .  Extend to ZZ by symmetry.  TODO: use ~ zindbi. $)
  jm2.19lem4 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. ZZ )
      -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + ( I x. M
      ) ) ) ) ) $=
    ( wcel cz wa crmy co cdivides wbr cmul caddc cn0 cneg ad2antrr syl2anc wceq
    wb cc c2 cuz cr wo elznn0 wi jm2.19lem3 3expia adantr simplll simprl simprr
    cfv nn0z adantl simplr recnd znegclb syl mpbird zmulcl simpr syl121anc cmin
    zaddcl zcn ad2antrl mulneg1 oveq2d ad2antll mulcl addcl negsub pncan 3eqtrd
    breq2d bitr2d ex jaod expimpd syl5bi 3impia ) AUAUBUMEZCFEZDFEZGZBFEZACHIZA
    DHIZJKZWHADBCLIZMIZHIJKZSZWGBUCEZBNEZBOZNEZUDZGWCWFGZWNBUEWTWOWSWNWTWOGZWPW
    NWRWTWPWNUFWOWCWFWPWNABCDUGUHUIXAWRWNXAWRGZWMWHAWLWQCLIZMIZHIZJKZWJXBWCWDWL
    FEZWRWMXFSWCWFWOWRUJWTWDWOWRWCWDWEUKPZXBWEWKFEZXGWTWEWOWRWCWDWEULPXBWGWDXIX
    BWGWQFEZWRXJXAWQUNUOXBBTEZWGXJSXBBWTWOWRUPUQZBURUSUTXHBCVAQDWKVEQXAWRVBAWQC
    WLUGVCXBXEWIWHJXBXDDAHXBXDWLWKOZMIZWLWKVDIZDXBXCXMWLMXBXKCTEZXCXMRXLWTXPWOW
    RWDXPWCWECVFVGPZBCVHQVIXBWLTEZWKTEZXNXORXBDTEZXSXRWTXTWOWRWEXTWCWDDVFVJPZXB
    XKXPXSXLXQBCVKQZDWKVLQYBWLWKVMQXBXTXSXODRYAYBDWKVNQVOVIVPVQVRVSVTWAWB $.
    $( [26-Sep-2014] $)

  $( Lemma 2.19 of [JonesMatijasevic].  Transfer divisibility constraints
     between Y-values and their indices. $)
  jm2.19 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M || N <-> (
      A rmY M ) || ( A rmY N ) ) ) $=
    ( cfv wcel cz cdivides wbr crmy co wb cc0 wceq adantr oveq2d cr syl2anc cn0
    cc syl3anc c2 cuz w3a wa rmyeq0 3adant2 0dvds 3ad2ant3 frmy fovcl syl simpr
    3bitr4d breq1d simpl1 rmy0 eqtrd wne cmo wi 3adant3 dvds0 3ad2ant1 breqtrrd
    cabs oveq2 breq2d syl5ibrcom wn cle clt crp zre ad2antrr zcn simplr absrpcl
    3ad2ant2 simpll1 cn simpll3 simpll2 nnabscl zmodcl nn0abscl ltrmynn0 nn0ssz
    modlt mpbid sseldi rmyabs modcl modge0 absid 3brtr4d nn0re ltnle dvdsleabs2
    3syl necon3bid mtod ex impbid simpl2 simpl3 dvdsabsmod0 cmin cdiv cneg cmul
    necon4ad caddc modabsdifz znegcl jm2.19lem4 recnd subcl divcl mulneg1 mulcl
    syl121anc negsub divcan1 nncan 3eqtrrd bitr4d pm2.61dane ) AUAUBDZEZBFEZCFE
    ZUCZBCGHZABIJZACIJZGHZKBLYLBLMZUDZLCGHZLYOGHZYMYPYLYSYTKYQYLCLMZYOLMZYSYTYI
    YKUUAUUBKYJACUEUFYKYIYSUUAKYJCUGUHYLYOFEZYTUUBKYIYKUUCYJACFYHFIUIUJUFYOUGUK
    UMNYRBLCGYLYQULZUNYRYNLYOGYRYNALIJZLYRBLAIUUDOYRYIUUELMZYIYJYKYQUOAUPZUKUQU
    NUMYLBLURZUDZCBVEDZUSJZLMZYNAUUKIJZGHZYMYPUUIUULUUNYLUULUUNUTUUHYLUUNUULYNU
    UEGHYLYNLUUEGYLYNFEZYNLGHYIYJUUOYKABFYHFIUIUJVAZYNVBUKYIYJUUFYKUUGVCVDUULUU
    MUUEYNGUUKLAIVFVGVHNUUIUUNUUKLUUIUUKLURZUUNVIUUIUUQUDZUUNYNVEDZUUMVEDZVJHZU
    URUUTUUSVKHZUVAVIZUURUUMAUUJIJZUUTUUSVKUURUUKUUJVKHZUUMUVDVKHZUURCPEZUUJVLE
    ZUVEYLUVGUUHUUQYKYIUVGYJCVMUHZVNZUURBSEZUUHUVHYLUVKUUHUUQYJYIUVKYKBVOVRZVNY
    LUUHUUQVPZBVQZQZCUUJWHQUURYIUUKREZUUJREZUVEUVFKYIYJYKUUHUUQVSZUURYKUUJVTEZU
    VPYIYJYKUUHUUQWAUURYJUUHUVSYIYJYKUUHUUQWBZUVMBWCQCUUJWDQZYLUVQUUHUUQYJYIUVQ
    YKBWEVRVNAUUKUUJWFTWIUURUUTAUUKVEDZIJZUUMUURYIUUKFEZUUTUWCMUVRUURRFUUKWGUWA
    WJZAUUKWKQUURUWBUUKAIUURUUKPEZLUUKVJHZUWBUUKMUURUVGUVHUWFUVJUVOCUUJWLZQUURU
    VGUVHUWGUVJUVOCUUJWMQUUKWNQOUQUURYIYJUUSUVDMUVRUVTABWKQWOUURUUTPEZUUSPEZUVB
    UVCKUURUUMFEZUUTREUWIUURYIUWDUWKUVRUWEAUUKFYHFIUIUJQZUUMWEUUTWPWSUURUUOUUSR
    EUWJYLUUOUUHUUQUUPVNZYNWEUUSWPWSUUTUUSWQQWIUURUUOUWKUUMLURZUUNUVAUTUWMUWLUU
    RUUQUWNUUIUUQULUURUUKLUUMLUURYIUWDUULUUMLMKUVRUWEAUUKUEQWTWIYNUUMWRTXAXBXKX
    CUUIYJYKUUHYMUULKYIYJYKUUHXDZYIYJYKUUHXEZYLUUHULZBCXFTUUIYPYNACCUUKXGJZBXHJ
    ZXIZBXJJZXLJZIJZGHZUUNUUIYIYJYKUWTFEZYPUXDKYIYJYKUUHUOUWOUWPUUIUWSFEZUXEUUI
    UVGBPEZUUHUXFYLUVGUUHUVINZYLUXGUUHYJYIUXGYKBVMVRNUWQBCXMTUWSXNUKAUWTBCXOYAU
    UIUUMUXCYNGUUIUUKUXBAIUUIUXBCUWSBXJJZXIZXLJZCUXIXGJZUUKUUIUXAUXJCXLUUIUWSSE
    ZUVKUXAUXJMUUIUWRSEZUVKUUHUXMUUICSEZUUKSEZUXNYLUXOUUHYLCUVIXPNZUUIUUKUUIUVG
    UVHUWFUXHUUIUVKUUHUVHYLUVKUUHUVLNZUWQUVNQUWHQXPZCUUKXQQZUXRUWQUWRBXRTZUXRUW
    SBXSQOUUIUXOUXISEZUXKUXLMUXQUUIUXMUVKUYBUYAUXRUWSBXTQCUXIYBQUUIUXLCUWRXGJZU
    UKUUIUXIUWRCXGUUIUXNUVKUUHUXIUWRMUXTUXRUWQUWRBYCTOUUIUXOUXPUYCUUKMUXQUXSCUU
    KYDQUQYEOVGYFUMYG $.
    $( [24-Sep-2014] $)

  $( Lemma for ~ jm2.20 .  Express X and Y values as a binomial. $)
  jm2.21 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. ZZ ) ->
      ( ( A rmX ( N x. J ) ) + ( ( sqr ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY ( N x.
      J ) ) ) ) =
      ( ( ( A rmX N ) + ( ( sqr ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) ) ^ J )
      ) $=
    ( c2 cuz cfv wcel cz cmul co crmx cexp c1 cmin csqr crmy caddc wceq rmxyval
    wa cc cc0 wne crp rmbaserp rpcnne0 syl expmulz zmulcl sylan2 adantrr oveq1d
    sylan 3eqtr4d 3impb ) ADEFGZCHGZBHGZACBIJZKJADLJMNJOFZAUSPJIJQJZACKJUTACPJI
    JQJZBLJZRUPUQURTZTZAUTQJZUSLJZVFCLJZBLJZVAVCUPVFUAGVFUBUCTZVDVGVIRUPVFUDGVJ
    AUEVFUFUGVFCBUHUMVDUPUSHGVAVGRCBUIAUSSUJVEVBVHBLUPUQVBVHRURACSUKULUNUO $.
    $( [26-Sep-2014] $)

  $( what lemmas can be pulled out of these two to shrink them? $)

  ${
    $d A i x $.  $d N i x $.  $d J i x $.
    $( Lemma for ~ jm2.20 .  Applying binomial theorem and taking irrational
       part. $)
    jm2.22 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. NN0 ) ->
        ( A rmY ( N x. J ) ) = sum_ i e. { x e. ( 0 ... J ) | -. 2 || x }
            ( ( J _C i ) x. ( ( ( A rmX N ) ^ ( J - i ) ) x.
            ( ( ( A rmY N ) ^ i ) x. ( ( ( A ^ 2 ) - 1 ) ^ ( ( i - 1 ) / 2 ) )
        ) ) ) ) $=
      ( c2 wcel cz cn0 cmul co cc0 cexp wceq sseldi syl2anc syl3anc a1i adantrr
      cc cuz cfv w3a crmx cv cdivides wbr cfz crab cbc cmin c1 csqr crmy csu wn
      cdiv caddc wa nn0z syl3an3 nn0sscn frmx fovcl 3adant3 zsscn eluzelz zsqcl
      jm2.21 peano2zm 3syl 3ad2ant1 sqrcl syl frmy mulcl simp3 binom cin c0 cun
      rabnc rabxm fzfid simpl3 adantl bccl zcn nn0ssz adantr fznn0sub 3ad2antl3
      elfzelz expcl elfznn0 fsumsplit cfn wss fzfi ssrab2 ssfi mp2an weq notbid
      breq2 elrab zexpcl syl2an c4 syl22anc wb 2z 2ne0 divides2 mpbid cr nn0ge0
      cle 2pos divge0 elnn0z sylanbrc sylan2b mul12 mulcom 2nn0 expmul ad2antrl
      2re 2cn divcan2 oveq2d oveq1d 3eqtr4d eqtrd 3eqtrd cq zmulcl zssq fsumzcl
      simpr 0nn0 dec2dvds1 4nn0 nn0cni mul01i oveq1i ax-1cn addid2i breq2i mtbi
      1z eqtri omoe wne clt zre cn wo dvds0 ax-mp mpbiri con3i elnn0 sylib sylc
      orel2 nnm1nn0 fsummulc2 sqrth 3eqtr3rd expm1t mulexp sumeq2dv eqtr2d cdif
      rmspecsqrnq nn0ssq simp1 simp2 3ad2ant3 eqcomd biimpa nn0re sylan eqeltrd
      qirropth syl122anc simprd ) BFUAUBZGZEHGZDIGZUCZBEDJKZUDKZFAUEZUFUGZALDUH
      KZUIZDCUEZUJKZBEUDKZDUXAUKKZMKZBFMKZULUKKZUMUBZBEUNKZJKZUXAMKZJKZJKZCUOZN
      ZBUWOUNKZUWRUPZAUWSUIZUXBUXEUXIUXAMKZUXGUXAULUKKZFUQKZMKZJKZJKZJKZCUOZNZU
      WNUWPUXHUXPJKURKZUXNUXHUYFJKZURKZNZUXOUYGUSZUWNUYHUXCUXJURKDMKZUWSUXMCUOZ
      UYJUWMUWKUWLDHGZUYHUYMNDUTZBDEVIVAUWNUXCTGZUXJTGZUWMUYMUYNNUWNITUXCVBUWKU
      WLUXCIGUWMBEIUWJHUDVCVDVEZOUWNUXHTGZUXITGZUYRUWNUXGTGZUYTUWNHTUXGVFUWKUWL
      UXGHGZUWMUWKBHGUXFHGVUCFBVGBVHUXFVJVKVLZOUXGVMZVNZUWNHTUXIVFUWKUWLUXIHGZU
      WMBEHUWJHUNVOVDVEZOUXHUXIVPZPUWKUWLUWMVQUXCUXJCDVRQUWNUYNUXNUXRUXMCUOZURK
      UYJUWNUWTUXRUXMUWSCUWTUXRVSVTNUWNUWRAUWSWBRUWSUWTUXRWANUWNUWRAUWSWCRUWNLD
      WDUWNUXAUWSGZUSZUXBTGZUXLTGZUXMTGVULUXBHGZVUMVULUWMUXAHGZVUOUWKUWLUWMVUKW
      EVUKVUPUWNUXALDWMZWFUWMVUPUSUXBIGVUOUXADWGUXBUTVNPZUXBWHVNZVULUXETGZUXKTG
      ZVUNVULUYQUXDIGZVUTVULHTUXCVFUWNUXCHGZVUKUWNIHUXCWIUYSOWJZOUWMUWKVUKVVBUW
      LIUXALDWKWLZUXCUXDWNPZVULUYRUXAIGZVVAVULUYTVUAUYRVULVUBUYTVULHTUXGVFUWNVU
      CVUKVUDWJOZVUEVNZVULHTUXIVFUWNVUGVUKVUHWJOZVUIPVUKVVGUWNUXADWOZWFZUXJUXAW
      NPUXEUXKVPPUXBUXLVPPWPUWNVUJUYIUXNURUWNUYIUXRUXHUYEJKZCUOVUJUWNUXRUYEUXHC
      UXRWQGZUWNUWSWQGZUXRUWSWRVVNLDWSZUXQAUWSWTUWSUXRXAXBRZVUFUXAUXRGZUWNVUKFU
      XAUFUGZUPZUSZUYETGZUXQVVTAUXAUWSACXCUWRVVSUWQUXAFUFXEZXDXFZUWNVWAUSZVUMUY
      DTGZVWBUWNVUKVUMVVTVUSSZVWEVUTUYCTGZVWFUWNVUKVUTVVTVVFSZVWEUXSTGZUYBTGZVW
      HUWNVUKVWJVVTVULHTUXSVFUWNVUGVVGUXSHGZVUKVUHVVKUXIUXAXGXHZOSZVWEVUBUYAIGZ
      VWKUWNVUKVUBVVTVVHSZVWAVWOUWNVWAUYAHGZLUYAXRUGZVWOVWAFUXTUFUGZVWQVWAVUPVV
      TULHGZFULUFUGZUPZVWSVUKVUPVVTVUQWJVUKVVTUUAVWTVWAUULRVXBVWAFXILJKZULURKZU
      FUGVXALUUBUUCVXDULFUFVXDLULURKULVXCLULURXIXIUUDUUEUUFUUGULUUHUUIUUMUUJUUK
      RUXAULUUNXJVWAFHGZFLUUOZUXTHGZVWSVWQXKVXEVWAXLRVXFVWAXMRVUKVXGVVTVUKVUPVX
      GVUQUXAVJZVNWJFUXTXNQXOVWAUXTXPGZLUXTXRUGZFXPGZLFUUPUGZVWRVUKVXIVVTVUKVUP
      VXGVXIVUQVXHUXTUUQVKWJVWAUXAUURGZUXTIGVXJVWAUXALNZUPZVXMVXNUUSZVXMVVTVXOV
      UKVXNVVSVXNVVSFLUFUGZVXEVXQXLFUUTUVAUXALFUFXEUVBUVCWFVWAVVGVXPVUKVVGVVTVV
      KWJUXAUVDUVEVXNVXMUVGUVFZUXAUVHUXTXQVKVXKVWAYIRVXLVWAXSRUXTFXTXJUYAYAYBZW
      FZUXGUYAWNPZUXSUYBVPPZUXEUYCVPPZUXBUYDVPPYCUVIUWNUXRVVMUXMCVVRUWNVWAVVMUX
      MNVWDVWEVVMUXBUXHUYDJKZJKZUXMVWEUYTVUMVWFVVMVYENUWNVUKUYTVVTVVISZVWGVYCUX
      HUXBUYDYDQVWEVYDUXLUXBJVWEVYDUXEUXHUYCJKZJKZUXLVWEUYTVUTVWHVYDVYHNVYFVWIV
      YBUXHUXEUYCYDQVWEVYGUXKUXEJVWEUXSUXHUXAMKZJKZVYIUXSJKZVYGUXKVWEVWJVYITGZV
      YJVYKNVWNUWNVUKVYLVVTVULUYTVVGVYLVVIVVLUXHUXAWNPSUXSVYIYEPVWEVYGUXSUXHUYB
      JKZJKZVYJVWEUYTVWJVWKVYGVYNNVYFVWNVYAUXHUXSUYBYDQVWEVYMVYIUXSJVWEUYBUXHJK
      ZUXHUXTMKZUXHJKZVYMVYIVWEUYBVYPUXHJVWEUXHFUYAJKZMKZUXHFMKZUYAMKZVYPUYBVWE
      UYTFIGZVWOVYSWUANVYFWUBVWEYFRVXTUXHFUYAYGQVWEVYRUXTUXHMVWEUXTTGZFTGZVXFVY
      RUXTNVUKWUCUWNVVTVUKVUPVXGWUCVUQVXHUXTWHVKYHWUDVWEYJRVXFVWEXMRUXTFYKQYLVW
      EVYTUXGUYAMVWEVUBVYTUXGNZVWPUXGUVJZVNYMUVKYMVWEUYTVWKVYMVYONVYFVYAUXHUYBY
      EPVWEUYTVXMVYIVYQNVYFVWAVXMUWNVXRWFUXHUXAUVLPYNYLYOUWNVUKUXKVYKNZVVTVULUY
      TVUAVVGWUGVVIVVJVVLUXHUXIUXAUVMZQSYNYLYOYLYOYCUVNUVOYLYOYPUWNUXHTYQUVPGZU
      WPYQGUXPYQGUXNYQGUYFYQGUYKUYLXKUWKUWLWUIUWMBUVQVLUWNIYQUWPUVRUWNUWKUWOHGZ
      UWPIGUWKUWLUWMUVSZUWNUWLUYOWUJUWKUWLUWMUVTUWMUWKUYOUWLUYPUWAEDYRPZBUWOIUW
      JHUDVCVDPOUWNHYQUXPYSUWNUWKWUJUXPHGWUKWULBUWOHUWJHUNVOVDPOUWNHYQUXNYSUWNU
      WTUXMCUWTWQGZUWNVVOUWTUWSWRWUMVVPUWRAUWSWTUWSUWTXAXBRUXAUWTGUWNVUKVVSUSZU
      XMHGZUWRVVSAUXAUWSVWCXFUWNWUNUSZVUOUXLHGZWUOUWNVUKVUOVVSVURSWUPUXEHGZUXKH
      GWUQUWNVUKWURVVSVULVVCVVBWURVVDVVEUXCUXDXGPZSWUPUXKUXGUXAFUQKZMKZUXSJKZHW
      UPUXKVYKWVBWUPUYTVUAVVGWUGUWNVUKUYTVVSVVISZUWNVUKVUAVVSVVJSVUKVVGUWNVVSVV
      KYHWUHQWUPVYIWVAUXSJWUPVYIUXHFWUTJKZMKZVYTWUTMKZWVAWUPUXAWVDUXHMUWNVUKUXA
      WVDNVVSVULWVDUXAVULUXATGZWUDVXFWVDUXANVUKWVGUWNVUKHTUXAVFVUQOWFWUDVULYJRV
      XFVULXMRUXAFYKQUWBSYLWUPUYTWUBWUTIGZWVEWVFNWVCWUBWUPYFRWUNWVHUWNVUKVVGVVS
      WVHVVKVVGVVSUSZWUTHGZLWUTXRUGZWVHVVGVVSWVJVVGVXEVXFVUPVVSWVJXKVXEVVGXLRVX
      FVVGXMRUXAUTFUXAXNQUWCWVIUXAXPGZLUXAXRUGZVXKVXLWVKVVGWVLVVSUXAUWDWJVVGWVM
      VVSUXAXQWJVXKWVIYIRVXLWVIXSRUXAFXTXJWUTYAYBUWEZWFUXHFWUTYGQWUPVYTUXGWUTMW
      UPVUBWUEUWNVUKVUBVVSVVHSWUFVNYMYPYMYOWUPWVAHGZVWLWVBHGUWNVUCWVHWVOWUNVUDW
      VNUXGWUTXGXHUWNVUKVWLVVSVWMSWVAUXSYRPUWFUXEUXKYRPUXBUXLYRPYCYTOUWNHYQUYFY
      SUWNUXRUYECVVQVVRUWNVWAUYEHGZVWDVWEVUOUYDHGZWVPUWNVUKVUOVVTVURSVWEWURUYCH
      GZWVQUWNVUKWURVVTWUSSVWEVWLUYBHGZWVRUWNVUKVWLVVTVWMSUWNVUCVWOWVSVWAVUDVXS
      UXGUYAXGXHUXSUYBYRPUXEUYCYRPUXBUYDYRPYCYTOUXHUWPUXPUXNUYFUWGUWHXOUWI $.
      $( [26-Sep-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.  $d J a b $.
    $( Lemma for ~ jm2.20 .  Truncate binomial expansion p-adicly. $)
    jm2.23 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. NN ) -> ( ( A rmY N )
        ^ 3 ) || ( ( A rmY ( N x. J ) ) - ( J x. ( ( ( A rmX N ) ^ ( J - 1 ) )
        x. ( A rmY N ) ) ) ) ) $=
      ( va c2 wcel cz co c3 cexp cdivides wbr c1 cmul a1i cn0 syl2anc cc0 wceq
      cc vb cuz cfv cn w3a crmy cv cfz crab cbc crmx cmin cdiv csu cfn wss fzfi
      wn ssrab2 ssfi mp2an wa nn0ssz nnnn0 3ad2ant3 sseli elfzelz syl2an sseldi
      syl bccl simpl1 simpl2 frmx fovcl simpl3 adantl fznn0sub zexpcl csquarenn
      cdif rmspecnonsq nnz 3ad2ant1 cle breq2 notbid elrab simprbi 1z caddc clt
      3syl 0z 2z ax-1cn syl22anc wne wb 2ne0 syl3anc mpbid 3re elfzle1 sylanbrc
      cr nnm1nn0 2re 2pos elnn0z sylancl zmulcl 3adant3 3nn0 wo adantr ad2antlr
      simpr elfz biimpi imp 2cn mpbiri sylc jaodan mpbir2and sylancr 1nn0 expcl
      nn0sscn zsscn mulcl mulass oveq2d oveq1d 3eqtrd eqtrd eqtr2d oveq12d
      oveq2 eldifi weq 2nn 1lt2 3pm3.2i dvds0 ax-mp ndvdsp1 addid2i breq2i mtbi
      mp2 omoe peano2zm divides2 zre 0re zssre 3pos ltletrd elnnz nn0ge0 divge0
      frmy elfzel1 zsubcl subge0 mpbird fsumzcl dvdsmul2 csn jm2.22 syl3an3 cin
      c0 1lt3 1re ltnlei mpbi mto intnanrd sylnibr disjsn sylibr cun olcd nn0zi
      ad2antrr elfznn0 simplrr elnn0 elnn1uz2 df-ne pm2.21d uzp1 mulid1i pm2.24
      dvdsmul1 breqtri eluzle eqcomi fveq2i eleq2s sylan2 sylan2b mpdan elfzle2
      df-3 orcd pm2.61dane nn0uz eleqtri simp3 fzss1 sseld anim1d eleq1 anbi12d
      jca nn0ge0i nnge1 impbida elun elsn orbi12i bitri 3bitr4g eqrdv rmspecpos
      crp rpcn wi con3d sylbi orel2 fsumsplit fsummulc1 mulcom expadd zcn npcan
      3cn eqtr3d sumeq2dv 1nn nn0cn subidi div0i eqtri 0nn0 eqeltri oveq1 sumsn
      oveq1i bcn1 eqcomd exp1 exp0 mulid1 fsumcl pncan breqtrrd ) AEUBUCZFZCGFZ
      BUDFZUEZACUFHZIJHZEUAUGZKLZURZUAIBUHHZUIZBDUGZUJHZACUKHZBVVOULHZJHZAEJHMU
      LHZVVOMULHZEUMHZJHZVVHVVOIULHZJHZNHZNHZNHZDUNZVVINHZACBNHUFHZBVVQBMULHZJH
      ZVVHNHZNHZULHZKVVGVWIGFVVIGFZVVIVWJKLVVGVVNVWHDVVNUOFZVVGVVMUOFVVNVVMUPVW
      RIBUQVVLUAVVMUSZVVMVVNUTVAOZVVGVVOVVNFZVBZVVPGFVWGGFZVWHGFVXBPGVVPVCVVGBP
      FZVVOGFZVVPPFZVXAVVFVVDVXDVVEBVDZVEZVXAVVOVVMFZVXEVVNVVMVVOVWSVFZVVOIBVGZ
      VJZVVOBVKZVHZVIVXBVVSGFZVWFGFZVXCVXBVVQGFVVRPFZVXOVXBPGVVQVCVXBVVDVVEVVQP
      FZVVDVVEVVFVXAVLZVVDVVEVVFVXAVMZACPVVCGUKVNVOZQVIVXBVVFVXIVXQVVDVVEVVFVXA
      VPVXAVXIVVGVXJVQUDVVOIBVRQZVVQVVRVSQVXBVWCGFZVWEGFZVXPVVGVVTGFZVWBPFZVYCV
      XAVVDVVEVYEVVFVVDVVTUDVTWAFVVTUDFVYEAWBVVTUDVTUUAVVTWCWMWDVXAVWBGFZRVWBWE
      LZVYFVXAEVWAKLZVYGVXAVXEEVVOKLZURZMGFZEMKLZURZVYIVXLVXAVXIVYKVVLVYKUAVVOV
      VMUADUUBVVKVYJVVJVVOEKWFWGZWHZWIVYLVXAWJOVYNVXAERMWKHZKLZVYMRGFZEUDFZMEWL
      LZUEERKLZVYRURVYSVYTWUAWNUUCUUDUUEEGFZWUBWOEUUFUUGZERUUHUULVYQMEKMWPUUIUU
      JUUKZOVVOMUUMZWQVXAWUCERWRZVWAGFZVYIVYGWSZWUCVXAWOOWUGVXAWTOVXAVXIVXEWUHV
      XJVXKVVOUUNZWMZEVWAUUOZXAXBVXAVWAXFFZRVWAWELZEXFFZREWLLZVYHVXAWUHWUMWUKVW
      AUUPZVJVXAVXIWUNVXJVXIVVOUDFZVWAPFZWUNVXIVXERVVOWLLWURVXKVXIRIVVORXFFVXIU
      UQOIXFFZVXIXCOVXIGXFVVOUURVXKVIZRIWLLVXIUUSOVVOIBXDZUUTVVOUVAXEVVOXGZVWAU
      VBZWMVJWUOVXAXHOWUPVXAXIOVWAEUVCZWQVWBXJZXEZVVTVWBVSVHVXBVVHGFZVWDPFZVYDV
      XBVVDVVEWVHVXSVXTACGVVCGUFUVDVOZQVXAWVIVVGVXAVXIWVIVXJVXIVWDGFZRVWDWELZWV
      IVXIVXEIGFZWVKVXKVVOIBUVEVVOIUVFQVXIWVLIVVOWELZWVBVXIVVOXFFWUTWVLWVNWSWVA
      XCVVOIUVGXKUVHVWDXJXEVJZVQZVVHVWDVSQVWCVWEXLQVVSVWFXLQVVPVWGXLQZUVIVVGWVH
      IPFZVWQVVDVVEWVHVVFWVJXMZXNVVHIVSXKVWIVVIUVJQVVGVWPVWJBMUJHZVWMVVHMJHZVVT
      MMULHZEUMHZJHZNHZNHZNHZWKHZWWGULHZVWJVVGVWKWWHVWOWWGULVVGVWKVVLUARBUHHZUI
      ZVVPVVSVVHVVOJHZVWCNHZNHZNHZDUNZVVNWWODUNZMUVKZWWODUNZWKHWWHVVFVVDVVEVXDV
      WKWWPSVXGUAADBCUVLUVMVVGVVNWWRWWOWWKDVVGMVVNFZURVVNWWRUVNUVOSVVGMVVMFZVYN
      VBWWTVVGWXAVYNWXAURVVGWXAIMWELZMIWLLWXBURUVPMIUVQXCUVRUVSMIBXDUVTOUWAVVLV
      YNUAMVVMVVJMSVVKVYMVVJMEKWFWGWHUWBVVNMUWCUWDVVGDWWKVVNWWRUWEZVVGVVOWWJFZV
      YKVBZVXIVYKVBZVVOMSZXOZVVOWWKFZVVOWXCFZVVGWXEWXHVVGWXEVBZWXHVVOMWXKWXGVBW
      XGWXFWXKWXGXRUWFWXKVVOMWRZVBZWXFWXGWXMVXIVYKWXMVXIWVNVVOBWELZWXMVXEWVMBGF
      ZVXIWVNWXNVBWSWXEVXEVVGWXLWXDVXEVYKVVORBVGZXPXQWVMWXMIXNUWGOVVGWXOWXEWXLV
      VFVVDWXOVVEBWCVEZUWHVVOIBXSXAWXMVVOPFZVYKWXLWVNWXEWXRVVGWXLWXDWXRVYKVVOBU
      WIZXPXQVVGWXDVYKWXLUWJZWXKWXLXRWXRVYKWXLUEZWURVVORSZXOZWVNWXRVYKWYCWXLWXR
      WYCVVOUWKXTZWDWYAWURWVNWYBWURWYAWXGVVOVVCFZXOWVNVVOUWLWYAWXGWVNWYEWYAWXGW
      VNWYAWXGWVNWXLWXRWXGURZVYKWXLWYFVVOMUWMXTVEUWNYAWYEWYAVVOESZVVOEMWKHZUBUC
      ZFZXOWVNEVVOUWOWYAWYGWVNWYJWYAWYGVBZVYJVYKWVNWYKVYJEEKLZEEMNHZEKWUCVYLEWY
      MKLWOWJEMUWRVAEYBUWPUWSWYGVYJWYLWSWYAVVOEEKWFVQYCWXRVYKWXLWYGVMVYJWVNUWQZ
      YDWYJWVNWYAWVNVVOIUBUCWYIIVVOUWTWYHIUBIWYHUXHUXAUXBUXCVQYEUXDYEUXEWYAWYBV
      BVYJVYKWVNWYBVYJWYAWYBVYJWUBWUDVVOREKWFYCZVQWXRVYKWXLWYBVMWYNYDYEUXFXAWXE
      WXNVVGWXLWXDWXNVYKVVORBUXGXPXQYFWXTUXSUXIUXJVVGWXFWXEWXGVVGWXFWXEVVGVXIWX
      DVYKVVGVVMWWJVVOVVGIRUBUCZFVVFVVMWWJUPIPWYPXNUXKUXLVVDVVEVVFUXMIRBUDUXNYG
      UXOUXPYAVVGWXGVBZWXEMWWJFZVYNWXGWXEWYRVYNVBWSVVGWXGWXDWYRVYKVYNVVOMWWJUXQ
      WXGVYJVYMVVOMEKWFWGUXRVQWYQWYRRMWELZMBWELZWYQVYLVYSWXOWYRWYSWYTVBWSVYLWYQ
      WJOVYSWYQWNOVVGWXOWXGWXQXPMRBXSXAWYSWYQMYHUXTOVVGWYTWXGVVFVVDWYTVVEBUYAVE
      XPYFVYNWYQWUEOYFYEUYBVVLVYKUAVVOWWJVYOWHZWXJVXAVVOWWRFZXOWXHVVOVVNWWRUYCV
      XAWXFXUBWXGVYPDMUYDUYEUYFUYGUYHWWKUOFZVVGWWJUOFWWKWWJUPXUCRBUQVVLUAWWJUSZ
      WWJWWKUTVAOVVGWXIVBZVVPTFZWWNTFZWWOTFXUEPTVVPYJVVGVXDVXEVXFWXIVXHWXIWXDVX
      EWWKWWJVVOXUDVFZWXPVJZVXMVHVIXUEVVSTFZWWMTFZXUGXUEVVQTFZVXQXUJVVGXULWXIVV
      GPTVVQYJVVDVVEVXRVVFVYAXMVIZXPXUEVVFWXDVXQVVDVVEVVFWXIVPWXIWXDVVGXUHVQUDV
      VORBVRQVVQVVRYIZQXUEWWLTFZVWCTFZXUKVVGVVHTFZWXRXUOWXIVVGGTVVHYKWVSVIZWXIW
      XDWXRXUHWXSVJVVHVVOYIVHVVGVVTTFZVYFXUPWXIVVDVVEXUSVVFVVDVVTUYJFXUSAUYIVVT
      UYKVJWDZWXIVYGVYHVYFWXIVYIVYGWXIVXEVYKVYLVYNVYIXUIWXIWXDVYKXUAWIVYLWXIWJO
      VYNWXIWUEOWUFWQWXIWUCWUGWUHWUIWUCWXIWOOWUGWXIWTOWXIWXDVXEWUHXUHWXPWUJWMZW
      ULXAXBWXIWUMWUNWUOWUPVYHWXIWUHWUMXVAWUQVJWXIWURWUSWUNWXIWYBURZWYCWURWXIWX
      EXVBXUAWXDVYKXVBWXDWYBVYJWYBVYJUYLWXDWYOOUYMYAUYNWXIWXDWXRWYCXUHWXSWYDWMW
      YBWURUYOYDWVCWVDWMWUOWXIXHOWUPWXIXIOWVEWQWVFXEVVTVWBYIZVHWWLVWCYLQVVSWWMY
      LQVVPWWNYLQUYPVVGWWQVWJWWSWWGWKVVGVWJVVNVWHVVINHZDUNWWQVVGVVNVWHVVIDVWTVV
      GXUQWVRVVITFZXURXNVVHIYIXKZVXBGTVWHYKWVQVIZUYQVVGVVNXVDWWODVXBXVDVVPVWGVV
      INHZNHZWWOVXBXUFVWGTFZXVEXVDXVISVXBPTVVPYJVXNVIVXBXUJVWFTFZXVJVXBXULVXQXU
      JVVGXULVXAXUMXPVYBXUNQZVXBXUPVWETFZXVKVVGXUSVYFXUPVXAXUTWVGXVCVHZVVGXUQWV
      IXVMVXAXURWVOVVHVWDYIVHZVWCVWEYLQZVVSVWFYLQVVGXVEVXAXVFXPZVVPVWGVVIYMXAVX
      BXVHWWNVVPNVXBXVHVVSVWFVVINHZNHZWWNVXBXUJXVKXVEXVHXVSSXVLXVPXVQVVSVWFVVIY
      MXAVXBXVRWWMVVSNVXBXVRVWCVWEVVINHZNHZXVTVWCNHZWWMVXBXUPXVMXVEXVRXWASXVNXV
      OXVQVWCVWEVVIYMXAVXBXUPXVTTFZXWAXWBSXVNVXBXVMXVEXWCXVOXVQVWEVVIYLQVWCXVTU
      YRQVXBXVTWWLVWCNVXBVVHVWDIWKHZJHZXVTWWLVXBXUQWVIWVRXWEXVTSVVGXUQVXAXURXPW
      VPWVRVXBXNOVVHVWDIUYSXAVXBXWDVVOVVHJVXBVVOTFZITFXWDVVOSVXBVXEXWFVXAVXEVVG
      VXLVQVVOUYTVJVUBVVOIVUAXKYNVUCYOYPYNYQYNYQVUDYRVVGMUDFWWGTFZWWSWWGSVUEVVG
      WVTTFZWWFTFZXWGVVFVVDXWHVVEVVFWVTPFZXWHVVFVXDVYLXWJVXGWJMBVKXKWVTVUFVJVEV
      VGVWMTFZWWETFZXWIVVGXULVWLPFZXWKXUMVVFVVDXWMVVEBXGVEVVQVWLYIQVVGWWATFZWWD
      TFZXWLVVGXUQMPFXWNXURYHVVHMYIXKVVGXUSWWCPFXWOXUTWWCRPWWCREUMHRWWBREUMMWPV
      UGVUNEYBWTVUHVUIZVUJVUKVVTWWCYIXKWWAWWDYLQVWMWWEYLQWVTWWFYLQZWWOWWGDMUDWX
      GVVPWVTWWNWWFNVVOMBUJYTWXGVVSVWMWWMWWENWXGVVRVWLVVQJVVOMBULYTYNWXGWWLWWAV
      WCWWDNVVOMVVHJYTWXGVWBWWCVVTJWXGVWAWWBEUMVVOMMULVULYOYNYSYSYSVUMYGYSYPVVG
      BWVTVWNWWFNVVGWVTBVVGVXDWVTBSVXHBVUOVJVUPVVGVVHWWEVWMNVVGWWEVVHMNHZVVHVVG
      WWAVVHWWDMNVVGXUQWWAVVHSXURVVHVUQVJVVGWWDVVTRJHZMVVGWWCRVVTJWWCRSVVGXWPOY
      NVVGXUSXWSMSXUTVVTVURVJYQYSVVGXUQXWRVVHSXURVVHVUSVJYRYNYSYSVVGVWJTFZXWGWW
      IVWJSVVGVWITFXVEXWTVVGVVNVWHDVWTXVGVUTXVFVWIVVIYLQXWQVWJWWGVVAQYQVVB $.
      $( [26-Sep-2014] $)
  $}

  $( Lemma 2.20 of [JonesMatijasevic], the "first step down lemma". $)
  jm2.20nn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN /\ N e. NN ) -> ( ( ( A rmY N
      ) ^ 2 ) || ( A rmY M ) <-> ( N x. ( A rmY N ) ) || M ) ) $=
    ( c2 wcel crmy co cdivides wbr cmul cc wceq syl2anc syl adantr cmin syl3anc
    cz cc0 c3 cuz cfv cn w3a cexp cdiv simp1 nnz 3ad2ant3 frmy fovcl sqval crmx
    wa zcn c1 cgcd zsqcl nn0ssz frmx sseldi simpr eqbrtrrd wi 3ad2ant2 muldvds1
    cn0 wb simpl1 jm2.19 mpbird simpl2 simpl3 nndivdivides mpbid nnm1nn0 zexpcl
    mpd nnssz zmulcl wne nncn nnne0 divcan2 oveq2d eqeltrd zsubcl 3nn0 a1i 2nn0
    cle 2z eluz1i nn0zi 2re 2lt3 ltleii mpbir2an dvdsexp jm2.23 dvdstr syl32anc
    3re imp dvds2sub oveq1d zsscn nncan mul12 3eqtrd gcdcom jm2.19lem1 rpexp12i
    breqtrd eqtrd syl112anc coprmdvds clt rmy0 3ad2ant1 nngt0 0z ltrmy sylanbrc
    elnnz dvdsmulcr dvdscmulr dvdsmul2 dvdssub2 syl31anc impbida ) ADUAUBZEZBUC
    EZCUCEZUDZACFGZDUEGZABFGZHIZCYQJGZBHIZYPYTUNZUUACBCUFGZJGZBHUUCUUAUUEHIZYQU
    UDHIZUUCYQYQJGZUUDYQJGZHIZUUGUUCYRUUHUUIHUUCYQKEZYRUUHLZYPUUKYTYPYQREZUUKYP
    YMCREZUUMYMYNYOUGZYOYMUUNYNCUHUIZACRYLRFUJUKMZYQUONZOZYQULZNUUCYRREZACUMGZU
    UDUPPGZUEGZREZUUIREZYRUVDUUIJGZHIZYRUVDUQGUPLZYRUUIHIZYPUVAYTYPUUMUVAUUQYQU
    RNZOZUUCUVBREZUVCVGEZUVEYPUVMYTYPVGRUVBUSYPYMUUNUVBVGEUUOUUPACVGYLRUMUTUKMV
    AZOZUUCUUDUCEZUVNUUCCBHIZUVQUUCUVRYQYSHIZUUCUUHYSHIZUVSUUCYRUUHYSHYPUULYTYP
    UUKUULUURUUTNZOYPYTVBZVCYPUVTUVSVDZYTYPUUMUUMYSREZUWCUUQUUQYPYMBREZUWDUUOYN
    YMUWEYOBUHVEZABRYLRFUJUKMZYQYQYSVFQOVRUUCYMUUNUWEUVRUVSVHYMYNYOYTVIZYPUUNYT
    UUPOZYPUWEYTUWFOACBVJQVKUUCYNYOUVRUVQVHYMYNYOYTVLYMYNYOYTVMBCVNMVOZUUDVPNZU
    VBUVCVQMZUUCUUDREZUUMUVFUUCUCRUUDVSUWJVAZYPUUMYTUUQOZUUDYQVTMUUCYRYSAUUEFGZ
    UUDUVDYQJGZJGZPGZPGZUVGHUUCUVAUWDUWSREZYTYRUWSHIZYRUWTHIZUVLYPUWDYTUWGOUUCU
    WPREZUWRREZUXAYPUXDYTYPUWPYSRYPUUEBAFYPBKEZCKEZCSWAZUUEBLZYNYMUXFYOBWBVEYOY
    MUXGYNCWBUIYOYMUXHYNCWCUIZBCWDQZWEUWGWFOUUCUWMUWQREZUXEUWNUUCUVEUUMUXLUWLUW
    OUVDYQVTMUUDUWQVTMZUWPUWRWGMZUWBUUCUVAYQTUEGZREZUXAYRUXOHIZUXOUWSHIZUXBUVLY
    PUXPYTYPUUMTVGEZUXPUUQUXSYPWHWIYQTVQMZOUXNYPUXQYTYPUUMDVGEZTYLEZUXQUUQUYAYP
    WJWIUYBYPUYBTREDTWKIDTWLWMTWHWNDTWOXCWPWQWRWIYQDTWSQZOUUCYMUUNUVQUXRUWHUWIU
    WJAUUDCWTQUVAUXPUXAUDUXQUXRUNUXBYRUXOUWSXAXDXBUVAUWDUXAUDYTUXBUNUXCYRYSUWSX
    EXDXBUUCUWTYSYSUWRPGZPGZUWRUVGUUCUWSUYDYSPUUCUWPYSUWRPUUCUUEBAFYPUXIYTUXKOZ
    WEXFWEUUCYSKEZUWRKEZUYEUWRLYPUYGYTYPRKYSXGUWGVAOUUCUXEUYHUXMUWRUONYSUWRXHMU
    UCUUDKEZUVDKEZUUKUWRUVGLUUCUWMUYIUWNUUDUONUUCUVEUYJUWLUVDUONUUSUUDUVDYQXIQX
    JXNUUCYQUVBUQGZUPLZUVIYPUYLYTYPUYKUVBYQUQGZUPYPUUMUVMUYKUYMLUUQUVOYQUVBXKMY
    PYMUUNUYMUPLUUOUUPACXLMXOOUUCUUMUVMUYAUVNUYLUVIVDUWOUVPUYAUUCWJWIUWKYQUVBDU
    VCXMXPVRUVAUVEUVFUDUVHUVIUNUVJYRUVDUUIXQXDXBVCUUCUUMUWMUUMYQSWAZUUJUUGVHUWO
    UWNUWOYPUYNYTYPYQUCEZUYNYPUUMSYQXRIUYOUUQYPASFGZSYQXRYMYNUYPSLYOAXSXTYPSCXR
    IZUYPYQXRIZYOYMUYQYNCYAUIYPYMSREZUUNUYQUYRVHUUOUYSYPYBWIUUPASCYCQVOVCYQYEYD
    ZYQWCNOYQYQUUDYFXPVOUUCUUMUWMUUNUXHUUFUUGVHUWOUWNUWIYPUXHYTUXJOCYQUUDYGXPVK
    UYFXNYPUUBUNZUVAAUUAFGZREZUWDYRVUBHIZVUBYSHIZYTYPUVAUUBUVKOYPVUCUUBYPYMUUAR
    EZVUCUUOYPUUNUUMVUFUUPUUQCYQVTMZAUUARYLRFUJUKMZOYPUWDUUBUWGOYPVUDUUBYPVUDYR
    YQUVBYQUPPGZUEGZYQJGZJGZHIZYPYRVUJYRJGZVULHYPVUJREZUVAYRVUNHIYPUVMVUIVGEZVU
    OUVOYPUYOVUPUYTYQVPNUVBVUIVQMZUVKVUJYRYHMYPVUNVUJUUHJGZVULYPYRUUHVUJJUWAWEY
    PVUJKEZUUKUUKVURVULLYPVUOVUSVUQVUJUONUURUURVUJYQYQXIQXOXNYPUVAVUCVULREZYRVU
    BVULPGZHIZVUDVUMVHUVKVUHYPUUMVUKREZVUTUUQYPVUOUUMVVCVUQUUQVUJYQVTMYQVUKVTMZ
    YPUVAUXPVVAREZUXQUXOVVAHIZVVBUVKUXTYPVUCVUTVVEVUHVVDVUBVULWGMUYCYPYMUUNUYOV
    VFUUOUUPUYTAYQCWTQUVAUXPVVEUDUXQVVFUNVVBYRUXOVVAXAXDXBYRVUBVULYIYJVKOVUAUUB
    VUEYPUUBVBVUAYMVUFUWEUUBVUEVHYMYNYOUUBVIYPVUFUUBVUGOYPUWEUUBUWFOAUUABVJQVOU
    VAVUCUWDUDVUDVUEUNYTYRVUBYSXAXDXBYK $.
    $( [27-Sep-2014] $)

  $( Lemma for ~ jm2.26 . $)
  jm2.25lem1 $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A
      || ( C - D ) \/ A || ( C - -u D ) ) ) ->
          ( ( A || ( D - B ) \/ A || ( D - -u B ) ) <-> ( A || ( C - B ) \/ A
      || ( C - -u B ) ) ) ) $=
    ( cz wcel wa cmin co cdivides wbr wo simpl1l simpl2l simpl2r simpl1r simpl3
    cneg simpr acongtr w3a syl222anc acongsym syl31anc impbida ) AEFZBEFZGZCEFZ
    DEFZGZACDHIJKACDRHIJKLZUAZADBHIJKADBRZHIJKLZACBHIJKACUNHIJKLZUMUOGUFUIUJUGU
    LUOUPUFUGUKULUOMUIUJUHULUONUIUJUHULUOOUFUGUKULUOPUHUKULUOQUMUOSACDBTUBUMUPG
    ZUFUJUIUGADCHIJKADCRHIJKLZUPUOUFUGUKULUPMZUIUJUHULUPOZUIUJUHULUPNZUFUGUKULU
    PPUQUFUIUJULURUSVAUTUHUKULUPQACDUCUDUMUPSADCBTUBUE $.
    $( [2-Oct-2014] $)

  ${
    $d A a b $.  $d M a b $.  $d N a b $.  $d I a b $.
    $( Lemma for ~ jm2.26 .  Remainders mod X(2n) are negaperiodic mod 2n. $)
    jm2.25 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. ZZ )
        -> ( ( A rmX N ) || ( ( A rmY ( M + ( I x. ( 2 x. N ) ) ) ) - ( A rmY M
        ) ) \/ ( A rmX N ) || ( ( A rmY ( M + ( I x. ( 2 x. N ) ) ) ) - -u ( A
        rmY M ) ) ) ) $=
      ( c2 wcel cz cmul caddc crmy cmin cdivides wbr sseldi syl2anc wceq oveq2d
      co cc c1 va vb cuz cfv wa crmx cneg wo cc0 simprl simprrr cn0 nn0ssz frmx
      wi fovcl simprrl frmy congid 2cn a1i zcn mulcl mul02 adantl addid1 adantr
      syl eqtrd ad2antll oveq1d breqtrrd orcd ex cv wb simpl peano2zdi ad2antrl
      eluzel2 zmulcl zaddcl znegcl zsubcl cexp rmxdbl nn0sscn sqcl ax-1cn npcan
      dvdsmul2 sqval mulass eqcomd syl3anc 3eqtrd dvdsmultr2 zsscn adddi mulid1
      w3a subneg breqtrd rmydbl mul32 dvds2add syl32anc adddir 1z addass mulid2
      mpd imp rmyadd addsub olcd jm2.25lem1 syl221anc pm5.74da weq oveq1 breq2d
      orbi12d imbi2d zindbi mpbid impcom 3impa ) AEUCUDZFZCGFZDGFZUEZBGFZADUFRZ
      ACBEDHRZHRZIRZJRZACJRZKRZLMZYOYSYTUGZKRZLMZUHZYNYJYMUEZUUFYNUUGYOACUIYPHR
      ZIRZJRZYTKRZLMZYOUUJUUCKRZLMZUHZUOZUUGUUFUOZYNUUGUUOYNUUGUEZUULUUNUURYOYT
      YTKRZUUKLUURYOGFZYTGFZYOUUSLMUURYJYLUUTYNYJYMUJZYNYJYKYLUKYJYLUEULGYOUMAD
      ULYIGUFUNUPZNZOUURYJYKUVAUVBYNYJYKYLUQACGYIGJURUPZOYOYTUSOUURUUJYTYTKUURU
      UICAJYMUUICPYNYJYMUUICUIIRZCYMUUHUICIYLUUHUIPZYKYLYPSFZUVGYLESFZDSFUVHUVI
      YLUTVADVBEDVCOYPVDVHVEQYKUVFCPZYLYKCSFZUVJCVBCVFVHVGVIVJQVKVLVMVNUUGYOACU
      AVOZYPHRZIRZJRZYTKRZLMZYOUVOUUCKRZLMZUHZUOUUGYOACUBVOZYPHRZIRZJRZYTKRZLMZ
      YOUWDUUCKRZLMZUHZUOUUGYOACUWATIRZYPHRZIRZJRZYTKRZLMZYOUWMUUCKRZLMZUHZUOUU
      PUUQUAUBBUWAGFZUUGUWIUWRUWSUUGUEZUUTUVAUWMGFZUWDGFZYOUWMUWDKRLMZYOUWMUWDU
      GZKRZLMZUHUWIUWRVPUWTYJYLUUTUWSYJYMUJZUWSYJYKYLUKZUVDOZUWTYJYKUVAUXGUWSYJ
      YKYLUQZUVEOUWTYJUWLGFZUXAUXGUWTYKUWKGFZUXKUXJUWTUWJGFYPGFZUXLUWTUWAUWSUUG
      VQZVRUWTEGFZYLUXMYJUXOUWSYMEAVTVSZUXHEDWAOZUWJYPWAOCUWKWBOAUWLGYIGJURUPOU
      WTYJUWCGFZUXBUXGUWTYKUWBGFZUXRUXJUWTUWSUXMUXSUXNUXQUWAYPWAOZCUWBWBOZAUWCG
      YIGJURUPOZUWTUXFUXCUWTYOUWDAYPUFRZHRZUXDKRZAUWCUFRZAYPJRZHRZIRZUXELUWTUUT
      UYEGFZUYHGFZYOUYELMZYOUYHLMZYOUYILMZUXIUWTUYDGFZUXDGFZUYJUWTUXBUYCGFZUYOU
      YBUWTYJUXMUYQUXGUXQYJUXMUEULGUYCUMAYPULYIGUFUNUPNOZUWDUYCWAOZUWTUXBUYPUYB
      UWDWCVHZUYDUXDWDOUWTUYFGFZUYGGFZUYKUWTYJUXRVUAUXGUYAYJUXRUEULGUYFUMAUWCUL
      YIGUFUNUPNOZUWTYJUXMVUBUXGUXQAYPGYIGJURUPOZUYFUYGWAOZUWTYOUWDUYCTIRZHRZUY
      ELUWTYOVUFLMZYOVUGLMZUWTYOEYOHRZYOHRZVUFLUWTVUJGFZUUTYOVUKLMUWTUXOUUTVULU
      XPUXIEYOWAOUXIVUJYOWKOUWTVUFEYOEWERZHRZTKRZTIRZVUNVUKUWTUYCVUOTIUWTYJYLUY
      CVUOPUXGUXHADWFOVKUWTVUNSFZTSFZVUPVUNPUWTUVIVUMSFZVUQUVIUWTUTVAZUWTYOSFZV
      USUWTULSYOWGUWTYJYLYOULFUXGUXHUVCONZYOWHVHEVUMVCOVURUWTWIVAZVUNTWJOUWTVUN
      EYOYOHRZHRZVUKUWTVUMVVDEHUWTVVAVUMVVDPVVBYOWLVHQUWTUVIVVAVVAVVEVUKPVUTVVB
      VVBUVIVVAVVAXAVUKVVEEYOYOWMWNWOVIWPVLUWTUUTUXBVUFGFVUHVUIUOUXIUYBUWTUYCUY
      RVRYOUWDVUFWQWOXLUWTVUGUYDUWDTHRZIRZUYDUWDIRZUYEUWTUWDSFZUYCSFVURVUGVVGPU
      WTGSUWDWRUYBNZUWTGSUYCWRUYRNVVCUWDUYCTWSWOUWTVVFUWDUYDIUWTVVIVVFUWDPVVJUW
      DWTVHQUWTUYEVVHUWTUYDSFZVVIUYEVVHPUWTGSUYDWRUYSNZVVJUYDUWDXBOWNWPXCUWTYOU
      YGLMZUYMUWTYOEADJRZHRZYOHRZUYGLUWTVVOGFZUUTYOVVPLMUWTUXOVVNGFZVVQUXPUWTYJ
      YLVVRUXGUXHADGYIGJURUPOZEVVNWAOUXIVVOYOWKOUWTUYGVUJVVNHRZVVPUWTYJYLUYGVVT
      PUXGUXHADXDOUWTUVIVVAVVNSFVVTVVPPVUTVVBUWTGSVVNWRVVSNEYOVVNXEWOVIVLUWTUUT
      VUAVUBVVMUYMUOUXIVUCVUDYOUYFUYGWQWOXLUUTUYJUYKXAUYLUYMUEUYNYOUYEUYHXFXMXG
      UWTUXEUYDUYHIRZUXDKRZUYIUWTUWMVWAUXDKUWTUWMAUWCYPIRZJRZVWAUWTUWLVWCAJUWTU
      WLCUWBTYPHRZIRZIRZUWCVWEIRZVWCUWTUWKVWFCIUWTUWASFVURUVHUWKVWFPUWTGSUWAWRU
      XNNVVCUWTGSYPWRUXQNZUWATYPXHWOQUWTVWHVWGUWTUVKUWBSFVWESFVWHVWGPUWTGSCWRUX
      JNUWTGSUWBWRUXTNUWTGSVWEWRUWTTGFZUXMVWEGFVWJUWTXIVAUXQTYPWAONCUWBVWEXJWOW
      NUWTVWEYPUWCIUWTUVHVWEYPPVWIYPXKVHQWPQUWTYJUXRUXMVWDVWAPUXGUYAUXQAUWCYPXN
      WOVIVKUWTVVKUYHSFUXDSFVWBUYIPVVLUWTGSUYHWRVUENUWTGSUXDWRUYTNUYDUYHUXDXOWO
      VIVLXPYOYTUWMUWDXQXRXSUAUBXTZUVTUWIUUGVWKUVQUWFUVSUWHVWKUVPUWEYOLVWKUVOUW
      DYTKVWKUVNUWCAJVWKUVMUWBCIUVLUWAYPHYAQQZVKYBVWKUVRUWGYOLVWKUVOUWDUUCKVWLV
      KYBYCYDUVLUWJPZUVTUWRUUGVWMUVQUWOUVSUWQVWMUVPUWNYOLVWMUVOUWMYTKVWMUVNUWLA
      JVWMUVMUWKCIUVLUWJYPHYAQQZVKYBVWMUVRUWPYOLVWMUVOUWMUUCKVWNVKYBYCYDUVLUIPZ
      UVTUUOUUGVWOUVQUULUVSUUNVWOUVPUUKYOLVWOUVOUUJYTKVWOUVNUUIAJVWOUVMUUHCIUVL
      UIYPHYAQQZVKYBVWOUVRUUMYOLVWOUVOUUJUUCKVWPVKYBYCYDUVLBPZUVTUUFUUGVWQUVQUU
      BUVSUUEVWQUVPUUAYOLVWQUVOYSYTKVWQUVNYRAJVWQUVMYQCIUVLBYPHYAQQZVKYBVWQUVRU
      UDYOLVWQUVOYSUUCKVWRVKYBYCYDYEYFYGYH $.
      $( [2-Oct-2014] $)
  $}

  ${
    $d A a $.  $d N a $.  $d K a $.  $d M a $.
    $( Lemma for ~ jm2.26 .  Reverse direction is required to prove forward
       direction, so do it separatly. induction on difference between K and M,
       together with the addition formula fact that adding 2N only inverts
       sign. $)
    jm2.26a $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) /\ ( K e. ZZ /\ M e. ZZ
        ) ) -> ( ( ( 2 x. N ) || ( K - M ) \/ ( 2 x. N ) || ( K - -u M ) ) -> (
        ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) || ( ( A
        rmY K ) - -u ( A rmY M ) ) ) ) ) $=
      ( va c2 wcel cz wa co cmin cdivides wbr crmy cneg wo syl2anc caddc adantr
      wceq cuz cfv cmul crmx cv wrex wb 2z simplr zmulcl sylancr zsubcl divides
      adantl simplll simplrr simpllr simpr jm2.25 syl121anc oveq2 oveq2d cc zcn
      pncan3 syl2anr ad2antlr sylan9eqr eqidd acongeq12d mpbid rexlimdva sylbid
      simprl znegcl ad2antll w3a cn0 nn0ssz frmx fovcl sseldi simplrl frmy 3jca
      ex negcl syl rmyneg acongneg2 jaod ) AFUAUBZGZDHGZIZBHGZCHGZIZIZFDUCJZBCK
      JZLMZADUDJZABNJZACNJZKJLMXCXDXEOZKJLMZPZWTBCOZKJZLMZWSXBEUEZWTUCJZXATZEHU
      FZXHWSWTHGZXAHGZXBXOUGWSFHGWNXPUHWMWNWRUIFDUJUKZWRXQWOBCULUNEWTXAUMQWSXNX
      HEHWSXLHGZIZXNXHXTXNIZXCACXMRJZNJZXEKJLMXCYCXFKJLMPZXHXTYDXNXTWMWQWNXSYDW
      MWNWRXSUOZWOWPWQXSUPZWMWNWRXSUQZWSXSURZAXLCDUSUTSYAXCYCXDXEXEXNXTYCACXARJ
      ZNJXDXNYBYIANXMXACRVAVBXTYIBANWRYIBTZWOXSWQCVCGZBVCGZYJWPCVDZBVDZCBVEVFVG
      VBVHYAXEVIVJVKWFVLVMWSXKXMXJTZEHUFZXHWSXPXJHGZXKYPUGXRWSWPXIHGZYQWOWPWQVN
      WQYRWOWPCVOVPZBXIULQEWTXJUMQWSYOXHEHXTYOXHXTYOIZXCHGZXDHGZXEHGZVQZXGXCXDX
      FOKJLMPZXHXTUUDYOXTUUAUUBUUCXTWMWNUUAYEYGWOVRHXCVSADVRWLHUDVTWAWBQXTWMWPU
      UBYEWOWPWQXSWCABHWLHNWDWAQXTWMWQUUCYEYFACHWLHNWDWAQWESYTXCAXIXMRJZNJZAXIN
      JZKJLMXCUUGUUHOKJLMPZUUEXTUUIYOXTWMYRWNXSUUIYEWSYRXSYSSYGYHAXLXIDUSUTSYTX
      CUUGXDUUHXFYOXTUUGAXIXJRJZNJXDYOUUFUUJANXMXJXIRVAVBXTUUJBANWRUUJBTZWOXSWQ
      XIVCGZYLUUKWPWQYKUULYMCWGWHYNXIBVEVFVGVBVHXTUUHXFTZYOXTWMWQUUMYEYFACWIQSV
      JVKXCXDXEWJQWFVLVMWK $.
      $( [2-Oct-2014] $)
  $}

  $( Lemma for ~ jm2.26 .  Use ~ acongrep to find K', M' ~ K, M in [0,N]. thus
     Y(K') ~~ Y(M') and both are small; K' = M' on pain of contradicting 2.24,
     so K ~~ M $)
  jm2.26lem3 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K e. ( 0 ... N )
      /\ M e. ( 0 ... N ) ) /\ ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) )
      \/ ( A rmX N ) || ( ( A rmY K ) - -u ( A rmY M ) ) ) ) -> K = M ) $=
    ( cfv wcel wa cc0 co crmy wbr wceq cz syl2anc cr cle sseldi syl wb cc c2 cn
    cuz cfz crmx cmin cdivides cneg wo wne cabs caddc clt w3a wn simplll adantr
    elfzelz ad2antlr rmyabs zssre elfzle1 absid oveq2d eqtrd oveq12d frmy fovcl
    adantl c1 readdcl simpllr nnz peano2zm cn0 nn0ssre frmx nnnn0 nn0uz simplrl
    syl6eleq fzm1 biimpa elfzle2 lermy syl3anc mpbid simplrr wi le2add syl22anc
    mp2and recnd addcom id1 necomd simpr neeqtrd df-ne adantll ad3antrrr simprr
    sylib ad2antrr orel2 sylc eqbrtrd jaodan mpdan jm2.24 lelttrd necon3bid 0re
    rmyeq ad2antll le0neg2 letri3 biimpar simplr eqtr3d negeq0 mpbird eqtr4d ex
    a1i necon3d znegcl rmyneg 3jca zsscn fveq2d addcl abscl abstri zsubcl ltnle
    imp subeq0 dvdsleabs mtod negsub negcl nn0ssz absneg eqcomd breqtrrd simpr1
    eqbrtrrd simpr2 subneg simpr3 jca pm4.56 syld necon4ad 3impia ) AUAUCEZFZDU
    BFZGZBHDUDIZFZCUVAFZGZADUEIZABJIZACJIZUFIZUGKZUVEUVFUVGUHZUFIZUGKZUIZBCLZUU
    TUVDGZUVMBCUVOBCUJZUVFUKEZUVGUKEZULIZUVEUMKZUVFUVGUJZUVFUVJUJZUNZUVMUOZUVOU
    VPUWCUVOUVPGZUVTUWAUWBUWEUVSUVFUVGULIZUVEUMUWEUVQUVFUVRUVGULUWEUVQABUKEZJIZ
    UVFUWEUURBMFZUVQUWHLUURUUSUVDUVPUPZUVDUWIUUTUVPUVBUWIUVCBHDURUQZUSZABUTNUWE
    UWGBAJUWEBOFZHBPKZUWGBLUVDUWMUUTUVPUVDMOBVAUWKQZUSUVDUWNUUTUVPUVBUWNUVCBHDV
    BUQZUSBVCNVDVEUWEUVRACUKEZJIZUVGUWEUURCMFZUVRUWRLUWJUVDUWSUUTUVPUVCUWSUVBCH
    DURZVIZUSZACUTNUWEUWQCAJUWECOFZHCPKZUWQCLUVDUXCUUTUVPUVDMOCVAUXAQZUSUVDUXDU
    UTUVPUVCUXDUVBCHDVBZVIUSCVCNVDVEVFUWEUWFADVJUFIZJIZADJIZULIZUVEUWEUVFOFZUVG
    OFZUWFOFUWEMOUVFVAUWEUURUWIUVFMFZUWJUWLABMUUQMJVGVHZNQZUWEMOUVGVAUWEUURUWSU
    VGMFZUWJUXBACMUUQMJVGVHZNQZUVFUVGVKNUWEUXHOFZUXIOFZUXJOFUWEMOUXHVAUWEUURUXG
    MFZUXHMFUWJUWEDMFZUYAUWEUUSUYBUURUUSUVDUVPVLZDVMZRZDVNRZAUXGMUUQMJVGVHNQZUW
    EMOUXIVAUWEUURUYBUXIMFUWJUYEADMUUQMJVGVHNQZUXHUXIVKNUWEVOOUVEVPUWEUURUYBUVE
    VOFUWJUYEADVOUUQMUEVQVHZNQUWEBHUXGUDIZFZBDLZUIZUWFUXJPKZUWEDHUCEZFZUVBUYMUW
    EDVOUYOUWEUUSDVOFUYCDVRZRVSWAUUTUVBUVCUVPVTZUYPUVBUYMBHDWBWCNUWEUYKUYNUYLUW
    EUYKGZUVFUXHPKZUVGUXIPKZUYNUYSBUXGPKZUYTUYKVUBUWEBHUXGWDVIUWEVUBUYTSZUYKUWE
    UURUWIUYAVUCUWJUWLUYFABUXGWEWFUQWGUWEVUAUYKUWECDPKZVUAUWEUVCVUDUUTUVBUVCUVP
    WHZCHDWDRUWEUURUWSUYBVUDVUASUWJUXBUYEACDWEWFWGUQUWEUYTVUAGUYNWIZUYKUWEUXKUX
    LUXSUXTVUFUXOUXRUYGUYHUVFUVGUXHUXIWJWKUQWLUWEUYLGZUWFUVGUVFULIZUXJPUWEUWFVU
    HLZUYLUWEUVFTFZUVGTFZVUIUWEUVFUXOWMUWEUVGUXRWMUVFUVGWNNUQVUGUVGUXHPKZUVFUXI
    PKZVUHUXJPKZVUGCUXGPKZVULVUGCUYJFZVUOVUGCDLZUOZVUPVUQUIZVUPUVPUYLVURUVOUVPU
    YLGZCDUJVURVUTCBDUVPCBUJUYLUVPBCUVPWOWPUQUVPUYLWQWRCDWSXCWTVUGUYPUVCVUSUUTU
    YPUVDUVPUYLUUSUYPUURUUSDVOUYOUYQVSWAVIXAUVOUVCUVPUYLUUTUVBUVCXBXDUYPUVCVUSC
    HDWBWCNVUQVUPXEXFCHUXGWDRUWEVUOVULSZUYLUWEUURUWSUYAVVAUWJUXBUYFACUXGWEWFUQW
    GUWEVUMUYLUWEBDPKZVUMUWEUVBVVBUYRBHDWDRUWEUURUWIUYBVVBVUMSUWJUWLUYEABDWEWFW
    GUQUWEVULVUMGVUNWIZUYLUWEUXLUXKUXSUXTVVCUXRUXOUYGUYHUVGUVFUXHUXIWJWKUQWLXGX
    HXIUWEUURUYBUXJUVEUMKUWJUYEADXJNXKXGUWEUVPUWAUVOUVPWQUWEUURUWIUWSUVPUWASUWJ
    UWLUXBUURUWIUWSUNBCUVFUVGABCXNXLWFWGUWEUVFACUHZJIZUVJUWEBVVDUJZUVFVVEUJZUVO
    UVPVVFUVOBVVDBCUVOBVVDLZUVNUVOVVHGZBHLZUVNVVIUWMHOFZBHPKZUWNVVJUVDUWMUUTVVH
    UWOUSVVKVVIXMYEVVIBVVDHPUVOVVHWQUVOVVDHPKZVVHUVOUXDVVMUVCUXDUUTUVBUXFXOUVOU
    XCUXDVVMSUVDUXCUUTUXEVIZCXPRWGUQXGUVDUWNUUTVVHUWPUSUWMVVKGVVJVVLUWNGBHXQXRW
    KVVIVVJGZBHCVVIVVJWQZVVOCHLZVVDHLZVVOBVVDHUVOVVHVVJXSVVPXTVVOCTFZVVQVVRSUVO
    VVSVVHVVJUVOCVVNWMXDCYARYBYCXIYDYFYQUWEUURUWIVVDMFZVVFVVGSUWJUWLUWEUWSVVTUW
    EUVCUWSVUEUWTRCYGRUURUWIVVTUNBVVDUVFVVEABVVDXNXLWFWGUWEUURUWSVVEUVJLUWJUXBA
    CYHNWRYIYDUVOUWCUWDUVOUWCGZUVIUOZUVLUOZGUWDVWAVWBVWCVWAUVIUVEUVHUKEZPKZVWAV
    WDUVEUMKZVWEUOZVWAUVFUVJULIZUKEZVWDUVEUMVWAVWHUVHUKVWAVUJVUKVWHUVHLVWAMTUVF
    YJVWAUURUWIUXMUURUUSUVDUWCUPZUVDUWIUUTUWCUWKUSUXNNZQZVWAMTUVGYJVWAUURUWSUXP
    VWJUVDUWSUUTUWCUXAUSUXQNZQZUVFUVGUUANYKVWAVWIUVSUVEVWAVWHTFZVWIOFVWAVUJUVJT
    FZVWOVWLVWAVUKVWPVWNUVGUUBRZUVFUVJYLNVWHYMRVWAUVQOFZUVROFZUVSOFVWAVUJVWRVWL
    UVFYMRVWAVUKVWSVWNUVGYMRUVQUVRVKNZVWAMOUVEVAVWAUURUYBUVEMFZVWJUUTUYBUVDUWCU
    USUYBUURUYDVIXDUURUYBGVOMUVEUUCUYIQNZQZVWAVWIUVQUVJUKEZULIZUVSPVWAVUJVWPVWI
    VXEPKVWLVWQUVFUVJYNNVWAUVRVXDUVQULVWAVUKUVRVXDLVWNVUKVXDUVRUVGUUDUUERVDUUFU
    VOUVTUWAUWBUUGZXKUUHVWAVWDOFZUVEOFZVWFVWGSVWAUVHTFVXGVWAMTUVHYJVWAUXMUXPUVH
    MFZVWKVWMUVFUVGYONZQUVHYMRVXCVWDUVEYPNWGVWAVXAVXIUVHHUJZUVIVWEWIVXBVXJVWAVX
    KUWAUVOUVTUWAUWBUUIVWAVUJVUKVXKUWASVWLVWNVUJVUKGUVHHUVFUVGUVFUVGYRXLNYBUVEU
    VHYSWFYTVWAUVLUVEUVKUKEZPKZVWAVXLUVEUMKZVXMUOZVWAVXLUWFUKEZUVEUMVWAUVKUWFUK
    VWAVUJVUKUVKUWFLVWLVWNUVFUVGUUJNYKVWAVXPUVSUVEVWAUWFTFZVXPOFVWAVUJVUKVXQVWL
    VWNUVFUVGYLNUWFYMRVWTVXCVWAVUJVUKVXPUVSPKVWLVWNUVFUVGYNNVXFXKXGVWAVXLOFZVXH
    VXNVXOSVWAUVKTFVXRVWAMTUVKYJVWAUXMUVJMFZUVKMFZVWKVWAUXPVXSVWMUVGYGRUVFUVJYO
    NZQUVKYMRVXCVXLUVEYPNWGVWAVXAVXTUVKHUJZUVLVXMWIVXBVYAVWAVYBUWBUVOUVTUWAUWBU
    UKVWAVUJVWPVYBUWBSVWLVWQVUJVWPGUVKHUVFUVJUVFUVJYRXLNYBUVEUVKYSWFYTUULUVIUVL
    UUMXCYDUUNUUOUUP $.
    $( [3-Oct-2014] $)

  ${
    $d A k m $.  $d N k m $.  $d K k m $.  $d M k m $.
    $( Lemma 2.26 of [JonesMatijasevic], the "second step down lemma". $)
    jm2.26 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K e. ZZ /\ M e. ZZ )
        ) -> ( ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) ||
        ( ( A rmY K ) - -u ( A rmY M ) ) ) <-> ( ( 2 x. N ) || ( K - M ) \/ ( 2
        x. N ) || ( K - -u M ) ) ) ) $=
      ( vm vk c2 wcel wa cz co crmy cmin cdivides wbr cneg wo wi fovcl syl2anc
      cuz cfv cn crmx cmul cc0 cfz wrex acongrep ad2ant2l ad2ant2lr w3a simpl1l
      cv 2z nnz adantl zmulcl sylancr simplrl 3ad2antl1 simpl3l elfzelz simplrr
      syl simpl2r weq wb simpl2l simplll cn0 nn0ssz sseldi jm2.26a syl22anc mpd
      frmx frmy simpr acongtr syl222anc simpl3r acongsym syl31anc jm2.26lem3 id
      syl121anc eqidd acongeq12d mpbid 3exp1 exp3a rexlimdv sylanl2 impbid ) AG
      UAUBZHZDUCHZIZBJHZCJHZIZIZADUDKZABLKZACLKZMKNOXDXEXFPZMKNOQZGDUEKZBCMKNOX
      IBCPZMKNOQZXCXIEUNZCMKNOXIXLXJMKNOQZEUFDUGKZUHZXHXKRZWRXAXOWQWTDCEUIUJXCX
      MXPEXNXCXLXNHZXMXPXCXIFUNZBMKNOXIXRBPZMKNOQZFXNUHZXQXMIZXPRZWRWTYAWQXADBF
      UIUKXCXTYCFXNXCXRXNHZXTYCXCYDXTIZYBXHXKXCYEYBULZXHIZXIJHZWTXLJHZXAXIBXLMK
      NOXIBXLPZMKNOQZXMXKYGGJHDJHZYHUOYGWSYLWSXBYEYBXHUMZWRYLWQDUPZUQVEZGDURUSZ
      XCYEXHWTYBWSWTXAXHUTVAZYGXQYIXQXMXCYEXHVBZXLUFDVCVEZXCYEXHXAYBWSWTXAXHVDV
      AZYGYHYIWTXIXLBMKNOXIXLXSMKNOQZYKYPYSYQYGXTUUAYDXTXCYBXHVFZYGFEVGZXTUUAVH
      YGWSYDXQXDAXRLKZAXLLKZMKNOXDUUDUUEPZMKNOQZUUCYMYDXTXCYBXHVIZYRYGXDJHZUUDJ
      HZXFJHZUUEJHZXDUUDXFMKNOXDUUDXGMKNOQZXDXFUUEMKNOXDXFUUFMKNOQZUUGYGWQYLUUI
      XCYEXHWQYBWQWRXBXHVJVAZYOWQYLIVKJXDVLADVKWPJUDVQSVMTZYGWQXRJHZUUJUUOYGYDU
      UQUUHXRUFDVCVEZAXRJWPJLVRSTZYGWQXAUUKUUOYTACJWPJLVRSTZYGWQYIUULUUOYSAXLJW
      PJLVRSTYGUUIUUJXEJHZUUKXDUUDXEMKNOXDUUDXEPMKNOQZXHUUMUUPUUSYGWQWTUVAUUOYQ
      ABJWPJLVRSTUUTYGXTUVBUUBYGWQYLUUQWTXTUVBRUUOYOUURYQAXRBDVNVOVPYFXHVSXDUUD
      XEXFVTWAYGXICXLMKNOXICYJMKNOQZUUNYGYHYIXAXMUVCYPYSYTXQXMXCYEXHWBZXIXLCWCW
      DYGWQYLXAYIUVCUUNRUUOYOYTYSACXLDVNVOVPXDUUDXFUUEVTWAAXRXLDWEWGUUCXIXRXLBB
      UUCWFUUCBWHWIVEWJXIXLBWCWDUVDXIBXLCVTWAWKWLWMVPWLWMVPWRWQYLXBXKXHRYNABCDV
      NWNWO $.
      $( [2-Oct-2014] $)
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b N $.
    $( Lemma 2.15 of [JonesMatijasevic]. ` rmY ` is a polynomial for fixed N,
       so has the expected congruence property. $)
    jm2.15nn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ( ZZ>= ` 2 ) /\ N e. NN0 ) ->
        ( A - B ) || ( ( A rmY N ) - ( B rmY N ) ) ) $=
      ( c2 wcel cmin co crmy cdivides wbr wi cc0 c1 syl2anc wceq oveq12d breq2d
      cz oveq2 imbi2d va vb cuz cfv wa cv caddc eluzelz zsubcl syl2an 0z congid
      cn0 sylancl rmy0 oveqan12d breqtrrd 1z rmy1 cn pm3.43 w3a 3ad2ant2 2z a1i
      cmul simp2l nnz 3ad2ant1 frmy adantr zmulcl simp2r adantl peano2zm simp3r
      fovcl syl iddvds congmul syl322anc simp3l congsub rmyluc 3exp a2d 2nn0ind
      syl5 weq impcom 3impa ) ADUCUDZEZBWLEZCUMEZABFGZACHGZBCHGZFGZIJZWOWMWNUEZ
      WTXAWPAUAUFZHGZBXBHGZFGZIJZKXAWPALHGZBLHGZFGZIJZKXAWPAMHGZBMHGZFGZIJZKXAW
      PAUBUFZMFGZHGZBXPHGZFGZIJZKZXAWPAXOHGZBXOHGZFGZIJZKZXAWPAXOMUGGZHGZBYGHGZ
      FGZIJZKZXAWTKUAUBCXAWPLLFGZXIIXAWPREZLREWPYMIJWMAREZBREZYNWNDAUHZDBUHZABU
      IUJZUKWPLULUNWMWNXGLXHLFAUOBUOUPUQXAWPMMFGZXMIXAYNMREWPYTIJYSURWPMULUNWMW
      NXKMXLMFAUSBUSUPUQYAYFUEXAXTYEUEZKXOUTEZYLXAXTYEVAUUBXAUUAYKUUBXAUUAYKUUB
      XAUUAVBZWPDYBAVFGZVFGZXQFGZDYCBVFGZVFGZXRFGZFGZYJIUUCYNUUEREZUUHREZXQREZX
      RREZWPUUEUUHFGIJZXTWPUUJIJXAUUBYNUUAYSVCZUUCDREZUUDREZUUKUUQUUCVDVEZUUCYB
      REZYOUURUUCWMXOREZUUTUUBWMWNUUAVGZUUBXAUVAUUAXOVHZVIZAXORWLRHVJVQNZXAUUBY
      OUUAWMYOWNYQVKVCZYBAVLNZDUUDVLNUUCUUQUUGREZUULUUSUUCYCREZYPUVHUUCWNUVAUVI
      UUBWMWNUUAVMZUVDBXORWLRHVJVQNZXAUUBYPUUAWNYPWMYRVNVCZYCBVLNZDUUGVLNUUCWMX
      PREZUUMUVBUUBXAUVNUUAUUBUVAUVNUVCXOVOVRVIZAXPRWLRHVJVQNUUCWNUVNUUNUVJUVOB
      XPRWLRHVJVQNUUCYNUUQUUQUURUVHWPDDFGIJZWPUUDUUGFGIJZUUOUUPUUSUUSUVGUVMUUCY
      NUUQUVPUUPVDWPDULUNUUCYNUUTUVIYOYPYEWPWPIJZUVQUUPUVEUVKUVFUVLUUBXAXTYEVPU
      UCYNUVRUUPWPVSVRWPYBYCABVTWAWPDDUUDUUGVTWAUUBXAXTYEWBWPUUEUUHXQXRWCWAUUCY
      HUUFYIUUIFUUCWMUVAYHUUFOUVBUVDAXOWDNUUCWNUVAYIUUIOUVJUVDBXOWDNPUQWEWFWHXB
      LOZXFXJXAUVSXEXIWPIUVSXCXGXDXHFXBLAHSXBLBHSPQTXBMOZXFXNXAUVTXEXMWPIUVTXCX
      KXDXLFXBMAHSXBMBHSPQTXBXPOZXFXTXAUWAXEXSWPIUWAXCXQXDXRFXBXPAHSXBXPBHSPQTU
      AUBWIZXFYEXAUWBXEYDWPIUWBXCYBXDYCFXBXOAHSXBXOBHSPQTXBYGOZXFYKXAUWCXEYJWPI
      UWCXCYHXDYIFXBYGAHSXBYGBHSPQTXBCOZXFWTXAUWDXEWSWPIUWDXCWQXDWRFXBCAHSXBCBH
      SPQTWGWJWK $.
      $( [1-Oct-2014] $)
  $}

  $( this may be alternately handled by expanding the domain of rmX and rmY to include 1, using the Lucas sequence as a new definition.  we do not do this $)

  ${
    $d a b A $.  $d a b N $.
    $( Lemma 2.16 of [JonesMatijasevic].  This may be regarded as a special
       case of ~ jm2.15nn0 if ` rmY ` is redefined as described in
       ~ rmyluc . $)
    jm2.16nn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A - 1 ) || ( ( A
        rmY N ) - N ) ) $=
      ( wcel c2 c1 cmin co crmy cdivides wbr wi cc0 cz syl cmul syl2anc 3adant3
      wa wceq oveq12d va vb cn0 cuz cv caddc eluzelz peano2zm 0z congid sylancl
      cfv rmy0 oveq1d breqtrrd 1z cn pm3.43 w3a adantl eluzel2 simpr nnz adantr
      rmy1 frmy fovcl zmulcl jca simp3r iddvds congmul syl112anc simp3l congsub
      3jca a1i rmyluc cc nncn mulid1 oveq2d 2times ax-1cn pnncan syl3anc eqtr2d
      eqtrd 3exp a2d syl5 oveq2 id breq2d imbi2d weq 2nn0ind impcom ) BUCCADUDU
      LZCZAEFGZABHGZBFGZIJZWTXAAUAUEZHGZXEFGZIJZKWTXAALHGZLFGZIJZKWTXAAEHGZEFGZ
      IJZKWTXAAUBUEZEFGZHGZXPFGZIJZKZWTXAAXOHGZXOFGZIJZKZWTXAAXOEUFGZHGZYEFGZIJ
      ZKZWTXDKUAUBBWTXALLFGZXJIWTXAMCZLMCXAYJIJWTAMCZYKDAUGZAUHZNZUIXALUJUKWTXI
      LLFAUMUNUOWTXAEEFGZXMIWTYKEMCZXAYPIJYOUPXAEUJUKWTXLEEFAVEUNUOXTYDRWTXSYCR
      ZKXOUQCZYIWTXSYCURYSWTYRYHYSWTYRYHYSWTYRUSZXADYAAOGZOGZXQFGZDXOEOGZOGZXPF
      GZFGZYGIYTYKUUBMCZUUEMCZUSZXQMCZXPMCZRZXAUUBUUEFGIJZXSXAUUGIJYSWTUUJYRYSW
      TRZYKUUHUUIUUOYLYKWTYLYSYMUTZYNNZUUODMCZUUAMCZUUHWTUURYSDAVAUTZUUOYAMCZYL
      UUSUUOWTXOMCZUVAYSWTVBZYSUVBWTXOVCVDZAXOMWSMHVFVGPZUUPYAAVHPZDUUAVHPUUOUU
      RUUDMCZUUIUUTUUOUVBYQUVGUVDUPXOEVHUKZDUUDVHPVPQYSWTUUMYRUUOUUKUULUUOWTUUL
      UUKUVCUUOUVBUULUVDXOUHNZAXPMWSMHVFVGPUVIVIQYTYKUURUURUSZUUSUVGRZXADDFGIJZ
      XAUUAUUDFGIJZUUNYSWTUVJYRUUOYKUURUURUUQUUTUUTVPQYSWTUVKYRUUOUUSUVGUVFUVHV
      IQYSWTUVLYRUUOYKUURUVLUUQUUTXADUJPQYTYKUVAUVBUSZYLYQRZYCXAXAIJZUVMYSWTUVN
      YRUUOYKUVAUVBUUQUVEUVDVPQYSWTUVOYRUUOYLYQUUPYQUUOUPVQVIQYSWTXSYCVJYSWTUVP
      YRUUOYKUVPUUQXAVKNQXAYAXOAEVLVMXADDUUAUUDVLVMYSWTXSYCVNXAUUBUUEXQXPVOVMYS
      WTYGUUGSYRUUOYFUUCYEUUFFUUOWTUVBYFUUCSUVCUVDAXOVRPYSYEUUFSWTYSUUFXOXOUFGZ
      XPFGZYEYSUUEUVQXPFYSUUEDXOOGZUVQYSUUDXODOYSXOVSCZUUDXOSXOVTZXOWANWBYSUVTU
      VSUVQSUWAXOWCNWHUNYSUVTUVTEVSCZUVRYESUWAUWAUWBYSWDVQXOXOEWEWFWGVDTQUOWIWJ
      WKXELSZXHXKWTUWCXGXJXAIUWCXFXIXELFXELAHWLUWCWMTWNWOXEESZXHXNWTUWDXGXMXAIU
      WDXFXLXEEFXEEAHWLUWDWMTWNWOXEXPSZXHXSWTUWEXGXRXAIUWEXFXQXEXPFXEXPAHWLUWEW
      MTWNWOUAUBWPZXHYCWTUWFXGYBXAIUWFXFYAXEXOFXEXOAHWLUWFWMTWNWOXEYESZXHYHWTUW
      GXGYGXAIUWGXFYFXEYEFXEYEAHWLUWGWMTWNWOXEBSZXHXDWTUWHXGXCXAIUWHXFXBXEBFXEB
      AHWLUWHWMTWNWOWQWR $.
      $( [1-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    X and Y sequences 4: Diophantine representability of Y
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    jm2.27a1 $e |- ( ph -> A e. ( ZZ>= ` 2 ) ) $.
    jm2.27a2 $e |- ( ph -> B e. NN ) $.
    jm2.27a3 $e |- ( ph -> C e. NN ) $.
    ${
      jm2.27a4 $e |- ( ph -> D e. NN0 ) $.
      jm2.27a5 $e |- ( ph -> E e. NN0 ) $.
      jm2.27a6 $e |- ( ph -> F e. NN0 ) $.
      jm2.27a7 $e |- ( ph -> G e. NN0 ) $.
      jm2.27a8 $e |- ( ph -> H e. NN0 ) $.
      jm2.27a9 $e |- ( ph -> I e. NN0 ) $.
      jm2.27a10 $e |- ( ph -> J e. NN0 ) $.
      jm2.27a11 $e |- ( ph -> ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) )
          ) = 1 ) $.
      jm2.27a12 $e |- ( ph -> ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) )
          ) = 1 ) $.
      jm2.27a13 $e |- ( ph -> G e. ( ZZ>= ` 2 ) ) $.
      jm2.27a14 $e |- ( ph -> ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) )
          ) = 1 ) $.
      jm2.27a15 $e |- ( ph -> E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) ) ) $.
      jm2.27a16 $e |- ( ph -> F || ( G - A ) ) $.
      jm2.27a17 $e |- ( ph -> ( 2 x. C ) || ( G - 1 ) ) $.
      jm2.27a18 $e |- ( ph -> F || ( H - C ) ) $.
      jm2.27a19 $e |- ( ph -> ( 2 x. C ) || ( H - B ) ) $.
      jm2.27a20 $e |- ( ph -> B <_ C ) $.

      ${
        jm2.27a21 $e |- ( ph -> P e. ZZ ) $.
        jm2.27a22 $e |- ( ph -> D = ( A rmX P ) ) $.
        jm2.27a23 $e |- ( ph -> C = ( A rmY P ) ) $.
        jm2.27a24 $e |- ( ph -> Q e. ZZ ) $.
        jm2.27a25 $e |- ( ph -> F = ( A rmX Q ) ) $.
        jm2.27a26 $e |- ( ph -> E = ( A rmY Q ) ) $.
        jm2.27a27 $e |- ( ph -> R e. ZZ ) $.
        jm2.27a28 $e |- ( ph -> I = ( G rmX R ) ) $.
        jm2.27a29 $e |- ( ph -> H = ( G rmY R ) ) $.
        $( Lemma for ~ jm2.27 .  Reverse direction after existential
           quantifiers are expanded. $)
        jm2.27a $p |- ( ph -> C = ( A rmY B ) ) $=
          ( crmy co wceq c2 cmul cmin cdivides wbr cneg wo cz wcel 2z cn zmulcl
          nnz syl sylancr cn0 nn0z congsym syl22anc cuz cfv cc0 cle nn0ge0 rmy0
          c1 eqcomd 3brtr4d wb a1i lermy syl3anc mpbird elnn0z sylanbrc syl2anc
          0z jm2.16nn0 oveq1d breqtrrd wa zsubcl dvdstr mp2and congtr syl222anc
          wi peano2zm orcd caddc zsqcl dvdsmul2 peano2zdi dvdsmultr2 mpd eqtr3d
          cexp 3brtr3d clt cr zssre sseldi nn0p1nn nngt0 3syl ltrmy elnnz mpbid
          2nn eqeltrrd w3a elfz2nn0 nnnn0 mpbir3and nnsqcl mulgt0 jm2.20nn crmx
          nnmulcl muldvds2 eqbrtrd dvdscmul frmy fovcl eluzelz eqbrtrrd oveq12d
          jm2.15nn0 jm2.26 dvdsacongtr acongtr rmygeid acongeq oveq2d eqtr4d
          cfz ) ADBFVDVEZBCVDVEUQACFBVDACFVFZVGDVHVEZCFVIVEVJVKUVECFVLZVIVEVJVK
          VMZAUVEVNVOZCVNVOZHVNVOZFVNVOZUVECHVIVEVJVKZUVECHVLVIVEVJVKZVMUVEHFVI
          VEZVJVKUVEHUVFVIVEZVJVKVMZUVGAVGVNVOZDVNVOZUVHVPADVQVOZUVRQDVSVTZVGDV
          RWAZACVQVOZUVIPCVSVTZVAUOAUVLUVMAUVHUVILVNVOZUVJUVECLVIVEVJVKZUVELHVI
          VEZVJVKZUVLUWAUWCALWBVOZUWDUBLWCVTZVAAUVHUWDUVIUVELCVIVEVJVKUWEUWAUWI
          UWCUMUVELCWDWEAUVEKWLVIVEZVJVKZUWJUWFVJVKZUWGUKAUWJKHVDVEZHVIVEZUWFVJ
          AKVGWFWGZVOZHWBVOZUWJUWNVJVKUGAUVJWHHWIVKZUWQVAAUWRKWHVDVEZUWMWIVKZAW
          HLUWSUWMWIAUWHWHLWIVKUBLWJVTAUWPUWSWHVFUGKWKVTALUWMVCWMWNAUWPWHVNVOZU
          VJUWRUWTWOUGUXAAXCWPZVAKWHHWQWRWSHWTXAZKHXDXBALUWMHVIVCXEXFAUVHUWJVNV
          OZUWFVNVOZUWKUWLXGUWGXMUWAAKVNVOZUXDAKWBVOUXFUAKWCVTZKXNVTAUWDUVJUXEU
          WIVALHXHXBUVEUWJUWFXIWRXJUVECLHXKXLXOAVGGVHVEZVNVOZUVJUVKUVHUVEUXHVJV
          KZUXHUVNVJVKUXHUVOVJVKVMZUVPAUVQGVNVOZUXIVPURVGGVRWAVAUOUWAADGVJVKZUX
          JADUVCGVJUQAFUVCVHVEGVJVKZUVCGVJVKZAUVCVGYCVEZBGVDVEZVJVKZUXNADVGYCVE
          ZNWLXPVEZVGUXSVHVEZVHVEZUXPUXQVJAUXSUYAVJVKZUXSUYBVJVKZAUVQUXSVNVOZUY
          CVPAUVRUYEUVTDXQVTZVGUXSXRWAAUYEUXTVNVOUYAVNVOZUYCUYDXMUYFANANWBVOZNV
          NVOUDNWCVTXSZAUVQUYEUYGVPUYFVGUXSVRWAZUXSUXTUYAXTWRYAADUVCVGYCUQXEAIU
          YBUXQUIUTYBYDABUWOVOZGVQVOZFVQVOZUXRUXNWOOAUXLWHGYEVKZUYLURAUYNBWHVDV
          EZUXQYEVKZAWHIUYOUXQYEAWHUYBIYEAUXTYFVOWHUXTYEVKZUYAYFVOWHUYAYEVKZWHU
          YBYEVKAVNYFUXTYGUYIYHAUYHUXTVQVOUYQUDNYIUXTYJYKAVNYFUYAYGUYJYHAUYAVQV
          OZUYRAVGVQVOUXSVQVOZUYSYOAUVSUYTQDUUAVTVGUXSUUEWAUYAYJVTUXTUYAUUBWEUI
          XFAUYKUYOWHVFOBWKVTZAIUXQUTWMWNAUYKUXAUXLUYNUYPWOOUXBURBWHGYLWRWSGYMX
          AZAUVKWHFYEVKZUYMUOAVUCUYOUVCYEVKZAWHDUYOUVCYEAUVSWHDYEVKQDYJVTVUAADU
          VCUQWMWNAUYKUXAUVKVUCVUDWOOUXBUOBWHFYLWRWSFYMXAZBGFUUCWRYNAUVKUVCVNVO
          ZUXLUXNUXOXMUOADUVCVNUQUVTYPZURFUVCGUUFWRYAUUGAUVRUXLUVQUXMUXJXMUVTUR
          UVQAVPWPVGDGUUHWRYAABGUUDVEZBHVDVEZUVCVIVEVJVKZVUHVUIUVCVLVIVEVJVKZVM
          ZUXKAVUJVUKAVUHVNVOZVUIVNVOZUWMVNVOZVUFVUHVUIUWMVIVEZVJVKZVUHUWMUVCVI
          VEZVJVKVUJAJVUHVNUSAJWBVOJVNVOZTJWCVTZYPZAUYKUVJVUNOVABHVNUWOVNVDUUIU
          UJXBZALUWMVNVCUWIYPZVUGAVUHBKVIVEZVJVKZVVDVUPVJVKZVUQAJVUHVVDVJUSAVUS
          UXFBVNVOZJKBVIVEVJVKJVVDVJVKVUTUXGAUYKVVGOVGBUUKVTZUJJKBWDWEUULAUYKUW
          PUWQVVFOUGUXCBKHUUNWRAVUMVVDVNVOZVUPVNVOZVVEVVFXGVUQXMVVAAVVGUXFVVIVV
          HUXGBKXHXBAVUNVUOVVJVVBVVCVUIUWMXHXBVUHVVDVUPXIWRXJAJLDVIVEVUHVURVJUL
          USALUWMDUVCVIVCUQUUMYDVUHVUIUWMUVCXKXLXOAUYKUYLUVJUVKVULUXKWOOVUBVAUO
          BHFGUUOWEYNUXHHFUVEUUPXLUVECHFUUQXLAUVSCWHDUVBVEZVOZFVVKVOZUVDUVGWOQA
          VVLCWBVOZDWBVOZCDWIVKZAUVSVVLVVNVVOVVPYQWOQVQCDYRVTAUWBVVNPCYSVTAUVSV
          VOQDYSVTZUNYTAVVMFWBVOZVVOFDWIVKZAUVSVVMVVRVVOVVSYQWOQVQFDYRVTAUYMVVR
          VUEFYSVTZVVQAFUVCDWIAUYKVVRFUVCWIVKOVVTBFUURXBUQXFYTDCFUUSWRWSUUTUVA
          $.
          $( [4-Oct-2014] $)
      $}

      ${
        $d ph p q r $.  $d A p q r $.  $d B p q r $.  $d C p q r $.
        $d D p q r $.  $d E q r $.  $d F q r $.  $d G r $.  $d H r $.
        $d I r $.
        $( Lemma for ~ jm2.27 .  Expand existential quantifiers for reverse
           direction. $)
        jm2.27b $p |- ( ph -> C = ( A rmY B ) ) $=
          ( vp vq vr cv crmx co wceq crmy wa cz wrex c2 cexp cmin cmul cuz wcel
          c1 cfv cn0 wb nnz syl rmxycomplete syl3anc mpbid adantr nn0z ad2antrr
          cn ad3antrrr cdivides wbr cle simprl simprrl simprrr simplrl ad2antlr
          caddc simprr jm2.27a ex exp3a rexlimdv mpd ) AEBULUOZUPUQURZDBWRUSUQU
          RZUTZULVAVBZDBCUSUQURZAEVCVDUQBVCVDUQVIVEUQZDVCVDUQZVFUQVEUQVIURZXBUB
          ABVCVGVJZVHZEVKVHZDVAVHZXFXBVLLOADWAVHZXJNDVMVNBULEDVOVPVQAXAXCULVAAW
          RVAVHZXAXCAXLXAUTZXCAXMUTZGBUMUOZUPUQURZFBXOUSUQURZUTZUMVAVBZXCXNGVCV
          DUQXDFVCVDUQVFUQVEUQVIURZXSAXTXMUCVRXNXHGVKVHZFVAVHZXTXSVLAXHXMLVRAYA
          XMQVRAYBXMAFVKVHZYBPFVSVNVRBUMGFVOVPVQXNXRXCUMVAXNXOVAVHZXRXCXNYDXRUT
          ZXCXNYEUTZJHUNUOZUPUQURZIHYGUSUQURZUTZUNVAVBZXCYFJVCVDUQHVCVDUQVIVEUQ
          IVCVDUQVFUQVEUQVIURZYKAYLXMYEUEVTYFHXGVHZJVKVHZIVAVHZYLYKVLAYMXMYEUDV
          TAYNXMYETVTAYOXMYEAIVKVHZYOSIVSVNVTHUNJIVOVPVQYFYJXCUNVAYFYGVAVHZYJXC
          YFYQYJUTZXCYFYRUTBCDEWRXOYGFGHIJKAXHXMYEYRLWBACWAVHXMYEYRMWBAXKXMYEYR
          NWBAXIXMYEYROWBAYCXMYEYRPWBAYAXMYEYRQWBAHVKVHXMYEYRRWBAYPXMYEYRSWBAYN
          XMYEYRTWBAKVKVHXMYEYRUAWBAXFXMYEYRUBWBAXTXMYEYRUCWBAYMXMYEYRUDWBAYLXM
          YEYRUEWBAFKVIWKUQVCXEVFUQVFUQURXMYEYRUFWBAGHBVEUQWCWDXMYEYRUGWBAVCDVF
          UQZHVIVEUQWCWDXMYEYRUHWBAGIDVEUQWCWDXMYEYRUIWBAYSICVEUQWCWDXMYEYRUJWB
          ACDWEWDXMYEYRUKWBXNXLYEYRAXLXAWFVTXNWSYEYRAXLWSWTWGVTXNWTYEYRAXLWSWTW
          HVTXNYDXRYRWIYEXPXNYRYDXPXQWFWJYEXQXNYRYDXPXQWLWJYFYQYJWFYFYQYHYIWGYF
          YQYHYIWHWMWNWOWPWQWNWOWPWQWNWOWPWQ $.
          $( [4-Oct-2014] $)
      $}
    $}

    ${
      jm2.27c4 $e |- ( ph -> C = ( A rmY B ) ) $.
      jm2.27c5 $e |- D = ( A rmX B ) $.
      jm2.27c6 $e |- Q = ( B x. ( A rmY B ) ) $.
      jm2.27c7 $e |- E = ( A rmY ( 2 x. Q ) ) $.
      jm2.27c8 $e |- F = ( A rmX ( 2 x. Q ) ) $.
      jm2.27c9 $e |- G = ( A + ( ( F ^ 2 ) x. ( ( F ^ 2 ) - A ) ) ) $.
      jm2.27c10 $e |- H = ( G rmY B ) $.
      jm2.27c11 $e |- I = ( G rmX B ) $.
      jm2.27c12 $e |- J = ( ( E / ( 2 x. ( C ^ 2 ) ) ) - 1 ) $.
      $( Lemma for ~ jm2.27 .  Forward direction with substitutions. $)
      jm2.27c $p |- ( ph ->
      ( ( ( D e. NN0
            /\ E e. NN0
            /\ F e. NN0 )
         /\ ( G e. NN0
            /\ H e. NN0
            /\ I e. NN0 ) )
      /\ ( J e. NN0
         /\ ( ( ( ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1
                  /\ ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) ) ) = 1
                  /\ G e. ( ZZ>= ` 2 ) )
               /\ ( ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) ) ) = 1
                  /\ E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) )
                  /\ F || ( G - A ) ) )
            /\ ( ( ( 2 x. C ) || ( G - 1 )
                  /\ F || ( H - C ) )
               /\ ( ( 2 x. C ) || ( H - B )
                  /\ B <_ C ) ) ) ) ) ) $=
        ( cn0 wcel w3a c2 cexp co cmin cmul wceq cuz cfv caddc cdivides wbr cle
        c1 wa crmx cz cn nnz syl frmx fovcl syl2anc syl5eqel crmy cc0 2z zmulcl
        eqeltrrd sylancr frmy rmy0 2nn nnmulcl nnnn0 nn0ge0 wb 0z lermy syl3anc
        a1i mpbid eqbrtrrd elnn0z sylanbrc 3jca 2nn0 cc nn0sscn sseldi nn0mulcl
        sqval eqeltrd cr nn0ssre clt eluz2b2 simplbi remulcl syl6breqr breqtrrd
        nnge1 zsqcl mpd nn0ssz dvdsmul1 zsscn eqtrd dvdstr mp2and oveq1d oveq2d
        wi 3brtr4d oveq1i oveq12d rmxynorm oveq2i oveq12i syl5eq ax-1cn sylancl
        3syl eqtr2d mulass eluzelz 1z zsubcl eqtr4d peano2zm sqcl syl322anc jca
        jca31 rmx1 1nn0 lermxnn0 rmxnn lemulge11 syl22anc letrd uzaddcl eluznn0
        nn0sub cdiv iddvds jm2.20nn mpbird dvdscmul 2cn mul32 nngt0 ltrmy elnnz
        rmydbl eqcomd nnsqcl nndivdivides nnm1nn0 wne nnne0 divcl npcan divcan1
        nncn pncan2 3eqtrd congid nnsscn eqbrtrd dvdsmultr2 subcl mulcl congsub
        muldvds1 subsub23 congmul congadd mulid2 jm2.15nn0 jm2.16nn0 rmygeid
        pncan3 ) AEUEUFZGUEUFZHUEUFZUGIUEUFZJUEUFZKUEUFZUGLUEUFZEUHUIUJZBUHUIUJ
        ZUTUKUJZDUHUIUJZULUJZUKUJZUTUMZHUHUIUJZUWSGUHUIUJZULUJZUKUJZUTUMZIUHUNU
        OZUFZUGZKUHUIUJZIUHUIUJUTUKUJZJUHUIUJZULUJZUKUJZUTUMZGLUTUPUJZUHUWTULUJ
        ZULUJZUMZHIBUKUJZUQURZUGZVAUHDULUJZIUTUKUJZUQURZHJDUKUJZUQURZVAUYEJCUKU
        JZUQURZCDUSURZVAZVAZVAZVAAUWJUWKUWLAEBCVBUJZUEQABUXIUFZCVCUFZUYPUEUFMAC
        VDUFZUYRNCVEVFZBCUEUXIVCVBVGVHVIVJAGBUHFULUJZVKUJZUESAVUBVCUFZVLVUBUSUR
        VUBUEUFAUYQVUAVCUFZVUCMAUHVCUFZFVCUFZVUDVMAFCBCVKUJZULUJZVCRAUYRVUGVCUF
        ZVUHVCUFZUYTADVUGVCPADVDUFZDVCUFZODVEVFZVOZCVUGVNVIZVJZUHFVNVPZBVUAVCUX
        IVCVKVQVHVIZABVLVKUJZVLVUBUSAUYQVUSVLUMMBVRVFZAVLVUAUSURZVUSVUBUSURZAVU
        AUEUFZVVAAVUAVDUFZVVCAUHVDUFZFVDUFZVVDVSAFVUHVDRAUYSVUGVDUFVUHVDUFNADVU
        GVDPOVOCVUGVTVIVJZUHFVTVPZVUAWAVFZVUAWBVFAUYQVLVCUFZVUDVVAVVBWCMVVJAWDW
        GZVUQBVLVUAWEWFWHWIVUBWJWKVJAHBVUAVBUJZUETAUYQVUDVVLUEUFMVUQBVUAUEUXIVC
        VBVGVHVIVJZWLAUWMUWNUWOAUHUEUFUXJUWMWMAIBUXDUXDBUKUJZULUJZUPUJZUXIUAAUY
        QVVOUEUFZVVPUXIUFMAUXDUEUFZVVNUEUFZVVQAUXDHHULUJZUEAHWNUFZUXDVVTUMAUEWN
        HWOVVMWPZHWRVFZAUWLUWLVVTUEUFVVMVVMHHWQVIWSZABUXDUSURZVVSABVVTUXDUSABHV
        VTAUEWTBXAAUYQBVDUFZBUEUFZMUYQVWFUTBXBURBXCXDBWAYIZWPAUEWTHXAVVMWPZAHWT
        UFZVWJVVTWTUFVWIVWIHHXEVIABVVLHUSABUTVBUJZBVVLUSAUYQVWKBUMMBUUAVFAUTVUA
        USURZVWKVVLUSURZAVVDVWLVVHVUAXHVFAUYQUTUEUFZVVCVWLVWMWCMVWNAUUBWGVVIBUT
        VUAUUCWFWHWITXFAVWJVWJVLHUSURZUTHUSURZHVVTUSURVWIVWIAUWLVWOVVMHWBVFAHVD
        UFVWPAHVVLVDTAUYQVUDVVLVDUFMVUQBVUAUUDVIVJHXHVFHHUUEUUFUUGVWCXGAVWGVVRV
        WEVVSWCVWHVWDBUXDUUJVIWHZUXDVVNWQVIZVVOUHBUUHVIVJZIUHUUIVPAJICVKUJZUEUB
        AVWTVCUFZVLVWTUSURVWTUEUFAUXJUYRVXAVWSUYTICVCUXIVCVKVQVHVIZAIVLVKUJZVLV
        WTUSAUXJVXCVLUMVWSIVRVFAVLCUSURZVXCVWTUSURZACUEUFZVXDAUYSVXFNCWAVFZCWBV
        FAUXJVVJUYRVXDVXEWCVWSVVKUYTIVLCWEWFWHWIVWTWJWKVJAKICVBUJZUEUCAUXJUYRVX
        HUEUFVWSUYTICUEUXIVCVBVGVHVIVJWLAUWPUYOALGUXSUUKUJZUTUKUJZUEUDAVXIVDUFZ
        VXJUEUFAUXSGUQURZVXKAUHVUGUHUIUJZULUJZVUBUXSGUQAVXNUHBFVKUJZULUJZUQURZV
        XPVUBUQURZVXNVUBUQURZAVXMVXOUQURZVXQAVXTVUHFUQURZAVUHVUHFUQAVUJVUHVUHUQ
        URVUOVUHUULVFRXFAUYQVVFUYSVXTVYAWCMVVGNBFCUUMWFUUNAVXMVCUFZVXOVCUFZVUEV
        XTVXQXSAVUIVYBVUNVUGXIVFZAUYQVUFVYCMVUPBFVCUXIVCVKVQVHVIZVUEAVMWGUHVXMV
        XOUUOWFXJAVXPVXPBFVBUJZULUJZVUBUQAVXPVCUFZVYFVCUFVXPVYGUQURAVUEVYCVYHVM
        VYEUHVXOVNVPZAUEVCVYFXKAUYQVUFVYFUEUFMVUPBFUEUXIVCVBVGVHVIZWPVXPVYFXLVI
        AVUBUHVYFULUJVXOULUJZVYGAUYQVUFVUBVYKUMMVUPBFUVAVIAUHWNUFZVYFWNUFVXOWNU
        FVYKVYGUMVYLAUUPWGZAUEWNVYFWOVYJWPAVCWNVXOXMVYEWPUHVYFVXOUUQWFXNXGAVXNV
        CUFZVYHVUCVXQVXRVAVXSXSAVUEVYBVYNVMVYDUHVXMVNVPVYIVURVXNVXPVUBXOWFXPAUW
        TVXMUHULADVUGUHUIPXQZXRGVUBUMASWGZXTZAGVDUFZUXSVDUFZVXLVXKWCAGVCUFZVLGX
        BURVYRAGVUBVCSVURVJZAVUSVUBVLGXBAVLVUAXBURZVUSVUBXBURZAVVDWUBVVHVUAUURV
        FAUYQVVJVUDWUBWUCWCMVVKVUQBVLVUAUUSWFWHAVUSVLVUTUVBVYPXTGUUTWKAVVEUWTVD
        UFZVYSVSAVUKWUDODUVCVFUHUWTVTVPZGUXSUVDVIWHVXIUVEVFVJAUXKUYDUYNAUXCUXHU
        XJAUXBUYPUHUIUJZUWSVXMULUJZUKUJZUTAUWQWUFUXAWUGUKUWQWUFUMAEUYPUHUIQYAWG
        AUWTVXMUWSULVYOXRYBAUYQUYRWUHUTUMMUYTBCYCVIXNAUXGVVLUHUIUJZUWSVUBUHUIUJ
        ZULUJZUKUJZUTUXDWUIUXFWUKUKHVVLUHUITYAUXEWUJUWSULGVUBUHUISYAYDYEAUYQVUD
        WULUTUMMVUQBVUAYCVIYFZVWSWLAUXQUYAUYCAUXPVXHUHUIUJZUXMVWTUHUIUJZULUJZUK
        UJZUTUXLWUNUXOWUPUKKVXHUHUIUCYAUXNWUOUXMULJVWTUHUIUBYAYDYEAUXJUYRWUQUTU
        MVWSUYTICYCVIYFAUXTVXIUXSULUJZGAUXRVXIUXSULAUXRVXJUTUPUJZVXIALVXJUTUPLV
        XJUMAUDWGXQAVXIWNUFZUTWNUFZWUSVXIUMAGWNUFZUXSWNUFZUXSVLUVFZWUTAVCWNGXMW
        UAWPZAVYSWVCWUEUXSUVKVFZAVYSWVDWUEUXSUVGVFZGUXSUVHWFYGVXIUTUVIYHXNXQAWV
        BWVCWVDWURGUMWVEWVFWVGGUXSUVJWFYJAHHHVVNULUJZULUJZUYBUQAHVCUFZWVHVCUFZH
        WVIUQURAUEVCHXKVVMWPZAWVJVVNVCUFZWVKWVLAUEVCVVNXKVWQWPZHVVNVNVIHWVHXLVI
        AUYBVVPBUKUJZVVOWVIUYBWVOUMAIVVPBUKUAYAWGABWNUFZVVOWNUFWVOVVOUMAUEWNBWO
        VWHWPZAUEWNVVOWOVWRWPBVVOUVLVIAVVOVVTVVNULUJZWVIAUXDVVTVVNULVWCXQAVWAVW
        AVVNWNUFWVRWVIUMVWBVWBAUEWNVVNWOVWQWPHHVVNYKWFXNUVMXGZWLAUYGUYIUYMAUYEV
        VPBUTUTBUKUJZULUJZUPUJZUKUJZUYFUQAUYEVCUFZBVCUFZWWEVVOVCUFWWAVCUFZUYEBB
        UKUJUQURZUYEVVOWWAUKUJUQURZUYEWWCUQURAVUEVULWWDVMVUMUHDVNVPZAUYQWWEMUHB
        YLVFZWWJAUEVCVVOXKVWRWPAUTVCUFZWVTVCUFZWWFYMAWWKWWEWWLYMWWJUTBYNVPZUTWV
        TVNVPAWWDWWEWWGWWIWWJUYEBUVNVIZAWWDUXDVCUFZWWKWVMWWLUYEUXDUTUKUJZUQURZU
        YEVVNWVTUKUJUQURZWWHWWIAUEVCUXDXKVWDWPZWWKAYMWGZWVNWWMAUYEUXFWWPUQAUYEU
        WSGULUJZGULUJZUXFUQAUYEGUQURZUYEWXBUQURZAUYEDULUJZGUQURZWXCAWXEUXSGUQAW
        XEUHDDULUJZULUJZUXSAVYLDWNUFZWXIWXEWXHUMVYMAVDWNDUVOOWPZWXJUHDDYKWFAUWT
        WXGUHULAWXIUWTWXGUMWXJDWRVFXRYOVYQUVPAWWDVULVYTWXFWXCXSWWIVUMWUAUYEDGUW
        AWFXJAWWDWXAVCUFZVYTWXCWXDXSWWIAUWSVCUFZVYTWXKAUWRVCUFZWXLAWWEWXMWWJBXI
        VFUWRYPVFWUAUWSGVNVIWUAUYEWXAGUVQWFXJAUXFUWSGGULUJZULUJZWXBAUXEWXNUWSUL
        AWVBUXEWXNUMWVEGWRVFXRAUWSWNUFZWVBWVBWXBWXOUMAUWRWNUFZWVAWXPAWVPWXQWVQB
        YQVFYGUWRUTUVRYHZWVEWVEUWSGGYKWFYOXGAUXHWWPUXFUMZWUMAUXDWNUFZUXFWNUFZWV
        AUXHWXSWCAVWAWXTVWBHYQVFAWXPUXEWNUFZWYAWXRAWVBWYBWVEGYQVFUWSUXEUVSVIWVA
        AYGWGUXDUXFUTUWBWFWHXGZAWWDWWOWWKWWEWWEWWQWWGWWRWWIWWSWWTWWJWWJWYCWWNUY
        EUXDUTBBUVTYRUYEUXDUTVVNWVTUWCYRUYEBBVVOWWAUWDYRAIVVPUTWWBUKIVVPUMAUAWG
        AWWBBWVTUPUJZUTAWWAWVTBUPAWVTWNUFWWAWVTUMAVCWNWVTXMWWMWPWVTUWEVFXRAWVPW
        VAWYDUTUMWVQYGBUTUWIYHYJYBXGZAUYCUYBUYHUQURZUYIWVSAUYBVWTVUGUKUJZUYHUQA
        UXJUYQVXFUYBWYGUQURVWSMVXGIBCUWFWFAJVWTDVUGUKJVWTUMAUBWGPYBXGAWVJUYBVCU
        FZUYHVCUFZUYCWYFVAUYIXSWVLAIVCUFZWWEWYHAUXJWYJVWSUHIYLVFZWWJIBYNVIAJVCU
        FZVULWYIAJVWTVCUBVXBVJZVUMJDYNVIHUYBUYHXOWFXPAUYKUYLAUYGUYFUYJUQURZUYKW
        YEAUYFVWTCUKUJZUYJUQAUXJVXFUYFWYOUQURVWSVXGICUWGVIJVWTCUKUBYAXFAWWDUYFV
        CUFZUYJVCUFZUYGWYNVAUYKXSWWIAWYJWYPWYKIYPVFAWYLUYRWYQWYMUYTJCYNVIUYEUYF
        UYJXOWFXPACVUGDUSAUYQVXFCVUGUSURMVXGBCUWHVIPXGYSYTYTYSYT $.
        $( [4-Oct-2014] $)
    $}
  $}

  ${
    $d A d e f g h i j $.  $d B d e f g h i j $.  $d C d e f g h i j $.

    $( [JonesMatijasevic] lemma 2.27; rmY is a diophantine relation. 0 was
       excluded from the range of B and the lower limit of G was imposed
       because the source proof does not seem to work otherwise; quite possible
       I'm just missing something.  The source proof uses both i and I; i has
       been changed to j to avoid collision.  This theorem is basically nothing
       but substitution instances, all the work is done in ~ jm2.27a and
       ~ jm2.27c .  Once Diophantine relations have been defined, the content
       of the theorem is "rmY is Diophantine" $)
    jm2.27 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN /\ C e. NN ) -> ( C = ( A rmY
        B ) <->
        E. d e. NN0 E. e e. NN0 E. f e. NN0 E. g e. NN0 E. h e. NN0 E. i e. NN0
        E. j e. NN0
          ( ( ( ( ( d ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1
                /\ ( ( f ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( e ^ 2 ) ) ) = 1
                /\ g e. ( ZZ>= ` 2 ) )
             /\ ( ( ( i ^ 2 ) - ( ( ( g ^ 2 ) - 1 ) x. ( h ^ 2 ) ) ) = 1
                /\ e = ( ( j + 1 ) x. ( 2 x. ( C ^ 2 ) ) )
                /\ f || ( g - A ) ) )
          /\ ( ( ( 2 x. C ) || ( g - 1 )
                /\ f || ( h - C ) )
             /\ ( ( 2 x. C ) || ( h - B )
                /\ B <_ C ) ) ) ) ) $=
      ( c2 wcel co wceq cexp c1 cmin wa cn0 wrex cuz cfv cn w3a crmy cmul caddc
      cdivides wbr cle crmx cdiv simpl1 simpl2 simpl3 simpr eqid jm2.27c simpld
      cv simprd oveq1 oveq1d eqeq2d 3anbi2d anbi2d anbi1d rcla4ev eleq1 3anbi3d
      syl oveq2d eqeq1d 3anbi13d anbi12d rexbidv 3anbi1d rcla43ev syl2anc eqeq1
      breq2d 2rexbidv breq1 ex simpll1 ad3antrrr simpll2 simpll3 simplrl simprl
      simplrr simprr ad2antrr simp2l1 simp2l2 simp2l3 simp2r1 simp2r2 rexlimdva
      simplr simp2r3 simp3ll simp3lr simp3rl simp3rr jm2.27b rexlimdvva impbid
      3expb ) AKUAUBZLZBUCLZCUCLZUDZCABUEMZNZJUTZKOMZAKOMPQMZCKOMZUFMZQMZPNZEUT
      ZKOMZXSDUTZKOMZUFMZQMZPNZFUTZXJLZUDZHUTZKOMZYKKOMZPQMZGUTZKOMZUFMZQMZPNZY
      FIUTZPUGMZKXTUFMZUFMZNZYDYKAQMZUHUIZUDZRZKCUFMZYKPQMZUHUIZYDYRCQMZUHUIZRZ
      UULYRBQMZUHUIZBCUJUIZRZRZRZISTZHSTZGSTZFSTZESTZDSTJSTZXNXPUVIXNXPRZABUKMZ
      SLAKBXOUFMZUFMZUEMZSLAUVMUKMZSLUDZUVKKOMZYAQMZPNZUVOKOMZXSUVNKOMZUFMZQMZP
      NZYLUDZUUBUVNUUFNZUVOUUHUHUIZUDZRZUUNUVOUUOUHUIZRZUVARZRZISTZHSTZGSTFSTZU
      VIUVJUVPAUVTUVTAQMUFMUGMZSLUWQBUEMZSLUWQBUKMZSLUDZUVJUVPUWTRZUVNUUEULMPQM
      ZSLUVSUWDUWQXJLZUDZUWSKOMZUWQKOMZPQMZUWRKOMZUFMZQMZPNZUVNUXBPUGMZUUEUFMZN
      ZUVOUWQAQMZUHUIZUDZRZUULUWQPQMZUHUIZUVOUWRCQMZUHUIZRZUULUWRBQMZUHUIZUUTRZ
      RZRZRZUVJABCUVKUVLUVNUVOUWQUWRUWSUXBXKXLXMXPUMXKXLXMXPUNXKXLXMXPUOXNXPUPU
      VKUQUVLUQUVNUQUVOUQUWQUQUWRUQUWSUQUXBUQURZUSZUSUVJUWTUXDUXKUWFUXPUDZRZUYG
      RZISTZUWPUVJUVPUWTUYKVAUVJUYIUYOUVJUXAUYIUYJVAUYNUYHIUXBSUUCUXBNZUYMUXRUY
      GUYPUYLUXQUXDUYPUWFUXNUXKUXPUYPUUFUXMUVNUYPUUDUXLUUEUFUUCUXBPUGVBVCVDVEVF
      VGVHVKUWNUYOUXDYOUXGYSUFMZQMZPNZUWFUXPUDZRZUXTUWJRZUVARZRZISTUXDYOUXIQMZP
      NZUWFUXPUDZRZUYGRZISTFGHUWQUWRUWSSSSYKUWQNZUWMVUDISVUJUWIVUAUWLVUCVUJUWEU
      XDUWHUYTVUJYLUXCUVSUWDYKUWQXJVIVJVUJUUBUYSUWGUXPUWFVUJUUAUYRPVUJYTUYQYOQV
      UJYQUXGYSUFVUJYPUXFPQYKUWQKOVBVCVCVLVMVUJUUHUXOUVOUHYKUWQAQVBWAVNVOVUJUWK
      VUBUVAVUJUUNUXTUWJVUJUUMUXSUULUHYKUWQPQVBWAVGVGVOVPYRUWRNZVUDVUIISVUKVUAV
      UHVUCUYGVUKUYTVUGUXDVUKUYSVUFUWFUXPVUKUYRVUEPVUKUYQUXIYOQVUKYSUXHUXGUFYRU
      WRKOVBVLVLVMVQVFVUKVUBUYCUVAUYFVUKUWJUYBUXTVUKUUOUYAUVOUHYRUWRCQVBWAVFVUK
      UUSUYEUUTVUKUURUYDUULUHYRUWRBQVBWAVGVOVOVPYNUWSNZVUIUYNISVULVUHUYMUYGVULV
      UGUYLUXDVULVUFUXKUWFUXPVULVUEUXJPVULYOUXEUXIQYNUWSKOVBVCVMVQVFVGVPVRVSUVG
      UWPUVSYJYLUDZUUJRZUVBRZISTHSTZGSTFSTUVSYEUWBQMZPNZYLUDZUUBUWFUUIUDZRZUVBR
      ZISTHSTZGSTFSTJDEUVKUVNUVOSSSXQUVKNZUVEVUPFGSSVVDUVCVUOHISSVVDUUKVUNUVBVV
      DYMVUMUUJVVDYCUVSYJYLVVDYBUVRPVVDXRUVQYAQXQUVKKOVBVCVMVQVGVGWBWBYFUVNNZVU
      PVVCFGSSVVEVUOVVBHISSVVEVUNVVAUVBVVEVUMVUSUUJVUTVVEYJVURUVSYLVVEYIVUQPVVE
      YHUWBYEQVVEYGUWAXSUFYFUVNKOVBVLVLVMVEVVEUUGUWFUUBUUIYFUVNUUFVTVEVOVGWBWBY
      DUVONZVVCUWOFGSSVVFVVBUWMHISSVVFVVAUWIUVBUWLVVFVUSUWEVUTUWHVVFVURUWDUVSYL
      VVFVUQUWCPVVFYEUVTUWBQYDUVOKOVBVCVMVEVVFUUIUWGUUBUWFYDUVOUUHUHWCVJVOVVFUU
      QUWKUVAVVFUUPUWJUUNYDUVOUUOUHWCVFVGVOWBWBVRVSWDXNUVHXPJDSSXNXQSLZYFSLZRZR
      ZUVFXPEFSSVVJYDSLZYKSLZRZRZUVDXPGHSSVVNYRSLZYNSLZRZRZUVCXPISVVRUUCSLZRZUV
      CXPVVTUVCRABCXQYFYDYKYRYNUUCVVNXKVVQVVSUVCXKXLXMVVIVVMWEWFVVNXLVVQVVSUVCX
      KXLXMVVIVVMWGWFVVNXMVVQVVSUVCXKXLXMVVIVVMWHWFVVNVVGVVQVVSUVCXNVVGVVHVVMWI
      WFVVNVVHVVQVVSUVCXNVVGVVHVVMWKWFVVNVVKVVQVVSUVCVVJVVKVVLWJWFVVNVVLVVQVVSU
      VCVVJVVKVVLWLWFVVRVVOVVSUVCVVNVVOVVPWJWMVVRVVPVVSUVCVVNVVOVVPWLWMVVRVVSUV
      CWTVVTUUKUVBYCYCYJYLUUJVVTUVBWNXIVVTUUKUVBYJYCYJYLUUJVVTUVBWOXIVVTUUKUVBY
      LYCYJYLUUJVVTUVBWPXIVVTUUKUVBUUBUUBUUGUUIYMVVTUVBWQXIVVTUUKUVBUUGUUBUUGUU
      IYMVVTUVBWRXIVVTUUKUVBUUIUUBUUGUUIYMVVTUVBXAXIVVTUUKUVBUUNUUNUUPUVAVVTUUK
      XBXIVVTUUKUVBUUPUUNUUPUVAVVTUUKXCXIVVTUUKUVBUUSUUSUUTUUQVVTUUKXDXIVVTUUKU
      VBUUTUUSUUTUUQVVTUUKXEXIXFWDWSXGXGXGXH $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d A a b $.  $d B a b $.
    jm2.27dlem1.1 $e |- A e. ( 1 ... B ) $.
    $( Lemma for ~ rmydioph .  Subsitution of a tuple restriction into a
       projection that doesn't care. $)
    jm2.27dlem1 $p |- ( a = ( b |` ( 1 ... B ) ) -> ( a ` A ) = ( b ` A ) ) $=
      ( cv c1 cfz co cres wceq cfv fveq1 wcel fvres ax-mp syl6eq ) CFZDFZGBHIZJ
      ZKARLAUALZASLZARUAMATNUBUCKEATSOPQ $.
      $( [11-Oct-2014] $)
  $}

  ${
    jm2.27dlem2.1 $e |- A e. ( 1 ... B ) $.
    jm2.27dlem2.2 $e |- C = ( B + 1 ) $.
    jm2.27dlem2.3 $e |- B e. NN $.
    $( Lemma for ~ rmydioph .  This theorem is used along with the next three
       to efficiently infer steps like ` 7 e. ( 1 ... 10 ) ` . $)
    jm2.27dlem2 $p |- A e. ( 1 ... C ) $=
      ( c1 cfz co wcel cz cle wbr w3a wb 1z caddc cn ax-mp cr nnz peano2z elfz1
      mp2b eqeltri mp2an elfzelz elfzle1 nnrei elfzle2 letrp1 breqtrri mpbir3an
      zrei mp3an ) AGCHIJZAKJZGALMZACLMZGKJCKJUPUQURUSNOPCBGQIZKEBRJBKJUTKJFBUA
      BUBUDUEAGCUCUFAGBHIJZUQDAGBUGSZVAURDAGBUHSAUTCLATJBTJABLMZAUTLMAVBUNBFUIV
      AVCDAGBUJSABUKUOEULUM $.
      $( [11-Oct-2014] $)
  $}

  ${
    jm2.27dlem3.1 $e |- A e. NN $.
    $( Lemma for ~ rmydioph .  Infer membership of the endpoint of a range. $)
    jm2.27dlem3 $p |- A e. ( 1 ... A ) $=
      ( cn wcel c1 cfz co elfz1end mpbi ) ACDAEAFGDBAHI $.
      $( [11-Oct-2014] $)

    jm2.27dlem4.2 $e |- B = ( A + 1 ) $.
    $( Lemma for ~ rmydioph .  Infer ` NN ` -hood of large numbers. $)
    jm2.27dlem4 $p |- B e. NN $=
      ( c1 caddc co cn wcel peano2nn ax-mp eqeltri ) BAEFGZHDAHIMHICAJKL $.
      $( [11-Oct-2014] $)
  $}

  ${
    jm2.27dlem5.1 $e |- A e. NN $.
    jm2.27dlem5.2 $e |- B = ( A + 1 ) $.
    jm2.27dlem5.3 $e |- ( 1 ... B ) C_ ( 1 ... C ) $.
    $( Lemma for ~ rmydioph .  Used with ~ sselii to infer membership of
       midpoints of range; ~ jm2.27dlem2 is deprecated. $)
    jm2.27dlem5 $p |- ( 1 ... A ) C_ ( 1 ... C ) $=
      ( c1 cfz co cn wcel wss caddc fzssp1 oveq2i syl6sseqr ax-mp sstri ) GAHIZ
      GBHIZGCHIAJKZSTLDUASGAGMIZHITGAJNBUBGHEOPQFR $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d a b c d e f g h i j k l $.

    $( Lemma 2.27 of [JonesMatijasevic] restated in terms of Diophantine
       sets. $)
    rmydioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( a ` 1 ) e. ( ZZ>= ` 2 )
        /\ ( a ` 3 ) = ( ( a ` 1 ) rmY ( a ` 2 ) ) ) } e. ( Dioph ` 3 ) $=
      ( vi c1 cfv c2 wcel c3 co wceq cn0 crab cexp cmin cmul cdivides wbr mp2an
      wa cmpt c10 vb vd vc ve vg vf vh cv crmy cfz cmap cn w3a caddc cle cc0 wo
      wrex cdioph wb cvv ovex 2nn jm2.27dlem3 df-3 jm2.27dlem2 anbi2d cz simplr
      clt adantl ad2antlr a1i syl3anc eleq1 pm5.32da ex pm5.32rd eqeq2d rabbiia
      bitrd cmzp 3nn0 1nn df-2 mzpproj eluzrabdioph mp3an 3nn elnnrabdioph wsbc
      2z c9 c8 c7 c6 c5 oveq1 oveq2d oveqan12rd eqeq1d oveq1d 3ad2ant3 3anbi12d
      c4 breq2d anbi1d anbi12d 3ad2ant1 sbc3ie sbcbiii oveq12d 3anbi23d breq12d
      fvex jm2.27dlem1 adantr 10nn 4nn df-5 5nn df-6 6nn df-7 7nn df-8 8nn df-9
      9nn jm2.27dlem5 sselii 2nn0 mzpexpmpt df-4 mzpsubmpt mzpmulmpt eqrabdioph
      df-10 dvdsrabdioph anrabdioph cuz elmapi mpan ffvelrn sylancl elnn0 sylib
      wf iba andi syl6bb syl frmy fovcl syl2anc rmy0 nngt0 ltrmy mpbid eqbrtrrd
      nnz elnnz sylanbrc syl5ibrcom pm4.71rd simpllr simpr jm2.27 oveq2 orbi12d
      0z eqtrd vex resex 3adant3 3ad2ant2 eqeq1 simp2 3anbi123d breq1 bi2anan9r
      cres 3adant1 breq1d sbc2ie 3bitri ssid mzpconstmpt 3anrabdioph lerabdioph
      nnnn0i 1z mzpaddmpt eqeltri 7rexfrabdioph eq0rabdioph orrabdioph ) CAUHZD
      ZEUUADZFZGUWRDZUWSEUWRDZUIHZIZRZAJCGUJHZUKHZKUXAUXBULFZUAUHZELHZUWSELHZCM
      HZUXBELHZNHZMHZCIZUBUHZELHZUXMUCUHZELHZNHZMHZCIZUDUHZUWTFZUMZUEUHZELHZUYE
      ELHZCMHZUFUHZELHZNHZMHZCIZUXTUGUHZCUNHZEUXNNHZNHZIZUXRUYEUWSMHZOPZUMZRZEU
      XBNHZUYECMHZOPZUXRUYLUXBMHZOPZRZVUFUYLUXCMHZOPZUXCUXBUOPZRZRZRZUGJURUEJUR
      UFJURUDJURUBJURUCJURUAJURZRZUXCULFZRZUXBUPIZUXCUPIZRZUQZRZAUXHKZGUSDZUXFV
      VFAUXHUWRUXHFZUXFUXAUXEVUTRZUXEVVCRZUQZRZVVFVVIVUTVVCUQZUXFVVMUTVVIUXCJFZ
      VVNVVIUXGJUWRUUHZEUXGFZVVOUXGVAFZVVIVVPCGUJVBZUWRJUXGUUBUUCEEGEVCVDZVEVCV
      FZUXGJEUWRUUDUUEUXCUUFUUGVVNUXEVVLUXAVVNUXEUXEVVNRVVLVVNUXEUUIUXEVUTVVCUU
      JUUKVGUULVVIUXAVVLVVEVVIUXARZVVJVVAVVKVVDVWBVUTUXEVUSVWBVUTUXEVUSUTVWBVUT
      RZUXEUXIUXERVUSVWCUXEUXIVWCUXIUXEUXDULFZVWCUXDVHFZUPUXDVJPVWDVWCUXAUXCVHF
      ZVWEVVIUXAVUTVIZVUTVWFVWBUXCUVAVKZUWSUXCVHUWTVHUIUUMUUNUUOVWCUWSUPUIHZUPU
      XDVJUXAVWIUPIZVVIVUTUWSUUPZVLVWCUPUXCVJPZVWIUXDVJPZVUTVWLVWBUXCUUQVKVWCUX
      AUPVHFZVWFVWLVWMUTVWGVWNVWCUVKVMVWHUWSUPUXCUURVNUUSUUTUXDUVBUVCUXBUXDULVO
      UVDUVEVWCUXIUXEVURVWCUXIRUXAVUTUXIUXEVURUTVVIUXAVUTUXIUVFVWBVUTUXIVIVWCUX
      IUVGUWSUXCUXBUCUBUDUFUEUGUAUVHVNVPWAVQVRVWBVVCUXEVVBVWBVVCUXEVVBUTVWBVVCR
      ZUXDUPUXBVWOUXDVWIUPVVCUXDVWIIVWBUXCUPUWSUIUVIVKUXAVWJVVIVVCVWKVLUVLVSVQV
      RUVJVPWAVTUXAAUXHKVVHFZVVEAUXHKVVHFZVVGVVHFGJFZEVHFZAVHUXGUKHZUWSSUXGWBDZ
      FZVWPWCWLVVRCUXGFVXBVVSCEGCCECWDVDZWEWDVFVEVCVFZAUXGCWFQAUWSEGWGWHVVAAUXH
      KVVHFZVVDAUXHKVVHFZVWQVUSAUXHKVVHFZVUTAUXHKVVHFZVXEUXIAUXHKVVHFZVURAUXHKV
      VHFZVXGVWRAVWTUXBSVXAFZVXIWCVVRGUXGFVXKVVSGWIVDZAUXGGWFQZAUXBGWJQVWRVUQUG
      TBUHZDZWKUEWMVXNDZWKUFWNVXNDZWKZUDWOVXNDZWKZUBWPVXNDZWKZUCWQVXNDZWKZUAXEV
      XNDZWKZAVXNUXGUWBZWKZBJCTUJHZUKHZKZTUSDZFVXJWCVYKVYEELHZCVXNDZELHZCMHZGVX
      NDZELHZNHZMHZCIZVYAELHZVYPVYCELHZNHZMHZCIZVXSUWTFZUMZVXPELHZVXSELHZCMHZVX
      QELHZNHZMHZCIZVYCVXOCUNHZEVYRNHZNHZIZVYAVXSVYNMHZOPZUMZRZEVYQNHZVXSCMHZOP
      ZVYAVXQVYQMHZOPZRZWVDVXQEVXNDZMHZOPZWVJVYQUOPZRZRZRZBVYJKZVYLVYHWVPBVYJVY
      HWVPUTVXNVYJFVYHUYGWUIUYKWULNHZMHZCIZUXTWUPUYSNHZIZVUCUMZRZVUHUXRVXQUXBMH
      ZOPZRZVUFVXQUXCMHZOPZVUNRZRZRZUDVXSWKZUBVYAWKZUCVYCWKZUAVYEWKZAVYGWKUXQWU
      BUXMWUCNHZMHZCIZWUGUMZWUOVYCWWAIZVYAVXSUWSMHZOPZUMZRZVUFWVEOPZVYAWWEOPZRZ
      WWJRZRZUAVYEWKZAVYGWKWVPVYFWWPVYGAVXNUXGBUVMUVNZVYDWWOVYEUAXEVXNXOZVYBWWN
      VYCUCWQVXNXOZVXTWWMVYAUBWPVXNXOZVXRWWLVXSUDWOVXNXOZVUQWWLUFUEUGVXQVXPVXOW
      NVXNXOWMVXNXOTVXNXOUYLVXQIZUYHVXPIZUYQVXOIZUMZVUEWWDVUPWWKWXTVUDWWCUYGWXT
      UYPWVTVUAWWBVUCWXQWXRUYPWVTUTWXSWXQWXRRUYOWVSCWXRWXQUYIWUIUYNWVRMUYHVXPEL
      WRWXQUYMWULUYKNUYLVXQELWRWSWTXAUVOWXSWXQVUAWWBUTWXRWXSUYTWWAUXTWXSUYRWUPU
      YSNUYQVXOCUNWRXBVSXCXDVGWXQWXRVUPWWKUTWXSWXQVUKWWGVUOWWJWXQVUJWWFVUHWXQVU
      IWWEUXROUYLVXQUXBMWRXFVGWXQVUMWWIVUNWXQVULWWHVUFOUYLVXQUXCMWRXFXGXHXIXHXJ
      XKXKXKXKXKWWPWXKVYGAWXLWWOWXJVYEUAWXMWWLWXJUCUBUDVYCVYAVXSWXNWXOWXPUXTVYC
      IZUXRVYAIZUYEVXSIZUMZWWDWXEWWKWXIWYDUYGWWTWWCWXDWYDUYDWWSUYFWUGUXQWYDUYCW
      WRCWYDUXSWUBUYBWWQMWYBWYAUXSWUBIWYCUXRVYAELWRUVPWYAWYBUYBWWQIWYCWYAUYAWUC
      UXMNUXTVYCELWRWSXIXLXAWYCWYAUYFWUGUTWYBUYEVXSUWTVOXCXMWYDWVTWUOWWBWXAVUCW
      XCWYCWYAWVTWUOUTWYBWYCWVSWUNCWYCWVRWUMWUIMWYCUYKWUKWULNWYCUYJWUJCMUYEVXSE
      LWRXBXBWSXAXCWYAWYBWWBWXAUTWYCUXTVYCWWAUVQXIWYDUXRVYAVUBWXBOWYAWYBWYCUVRW
      YCWYAVUBWXBIWYBUYEVXSUWSMWRXCXNUVSXHWYBWYCWWKWXIUTWYAWYBWYCRWWGWXHWWJWYCV
      UHWXFWYBWWFWXGWYCVUGWVEVUFOUYEVXSCMWRXFUXRVYAWWEOUVTUWAXGUWCXHXJXKXKWXJWV
      PAUAVYGVYEWXLWXMUWRVYGIZUXJVYEIZRZWXEWVCWXIWVOWYGWWTWUHWXDWVBWYGUXQWUAWWS
      WUFWUGWYGUXPVYTCWYFWYEUXKVYMUXOVYSMUXJVYEELWRWYEUXMVYPUXNVYRNWYEUXLVYOCMW
      YEUWSVYNELCGABVXDXPZXBXBZWYEUXBVYQELGGABVXLXPZXBZXLWTXAWYEWWSWUFUTWYFWYEW
      WRWUECWYEWWQWUDWUBMWYEUXMVYPWUCNWYIXBWSXAXQXDWYEWXDWVBUTWYFWYEWXAWUSWXCWV
      AWUOWYEWWAWURVYCWYEUYSWUQWUPNWYEUXNVYRENWYKWSWSVSWYEWXBWUTVYAOWYEUWSVYNVX
      SMWYHWSXFXMXQXHWYEWXIWVOUTWYFWYEWXHWVIWWJWVNWYEWXFWVFWXGWVHWYEVUFWVDWVEOW
      YEUXBVYQENWYJWSZUWDWYEWWEWVGVYAOWYEUXBVYQVXQMWYJWSXFXHWYEWWIWVLVUNWVMWYEV
      UFWVDWWHWVKOWYLWYEUXCWVJVXQMEGABVWAXPZWSXNWYEUXCWVJUXBVYQUOWYMWYJXNXHXHXQ
      XHUWEUWFVMVTWVCBVYJKVYLFZWVOBVYJKVYLFZWVQVYLFWUHBVYJKVYLFZWVBBVYJKVYLFZWY
      NWUABVYJKVYLFZWUFBVYJKVYLFZWUGBVYJKVYLFZWYPTJFZBVHVYIUKHZVYTSVYIWBDZFZBXU
      BCSXUCFZWYRTXRUWKZBXUBVYMSXUCFZBXUBVYSSXUCFZXUDBXUBVYESXUCFZEJFZXUGVYIVAF
      ZXEVYIFXUICTUJVBZCXEUJHVYIXEXEWQTXSXTWQWPTYAYBWPWOTYCYDWOWNTYEYFWNWMTYGYH
      WMTTYIYRVYIUWGYJYJZYJZYJZYJZYJZXEXSVDYKBVYIXEWFQYLBVYEEVYIYMQBXUBVYPSXUCF
      ZBXUBVYRSXUCFZXUHBXUBVYOSXUCFZXUEXURBXUBVYNSXUCFZXUJXUTXUKCVYIFXVAXULCCUJ
      HVYICCETWDWEEGTVCVEGXETWIYNXUQYJZYJZYJVXCYKBVYICWFQZYLBVYNEVYIYMQXUKCVHFX
      UEXULUWLBCVYIUWHQZBVYOCVYIYOQZBXUBVYQSXUCFZXUJXUSXUKGVYIFXVGXULUXGVYIGXVB
      VXLYKBVYIGWFQZYLBVYQEVYIYMQZBVYPVYRVYIYPQBVYMVYSVYIYOQXVEBVYTCTYQWHXUABXU
      BWUESXUCFZXUEWYSXUFBXUBWUBSXUCFZBXUBWUDSXUCFZXVJBXUBVYASXUCFZXUJXVKXUKWPV
      YIFXVMXULCWPUJHVYIWPXUOWPYCVDYKBVYIWPWFQZYLBVYAEVYIYMQXURBXUBWUCSXUCFZXVL
      XVFBXUBVYCSXUCFZXUJXVOXUKWQVYIFXVPXULCWQUJHVYIWQXUPWQYAVDYKBVYIWQWFQZYLBV
      YCEVYIYMQBVYPWUCVYIYPQBWUBWUDVYIYOQXVEBWUECTYQWHXUAVWSBXUBVXSSXUCFZWYTXUF
      WLXUKWOVYIFXVRXULCWOUJHVYIWOXUNWOYEVDYKBVYIWOWFQZBVXSETWGWHWUAWUFWUGBTUWI
      WHWUOBVYJKVYLFZWUSBVYJKVYLFZWVABVYJKVYLFZWYQXUABXUBWUNSXUCFZXUEXVTXUFBXUB
      WUISXUCFZBXUBWUMSXUCFZXWCBXUBVXPSXUCFZXUJXWDXUKWMVYIFXWFXULWMWMTWMYIVDYRY
      IVFBVYIWMWFQYLBVXPEVYIYMQBXUBWUKSXUCFZBXUBWULSXUCFZXWEBXUBWUJSXUCFZXUEXWG
      XVRXUJXWIXVSYLBVXSEVYIYMQXVEBWUJCVYIYOQBXUBVXQSXUCFZXUJXWHXUKWNVYIFXWJXUL
      CWNUJHVYIWNXUMWNYGVDYKBVYIWNWFQZYLBVXQEVYIYMQBWUKWULVYIYPQBWUIWUMVYIYOQXV
      EBWUNCTYQWHXUAXVPBXUBWURSXUCFZXWAXUFXVQBXUBWUPSXUCFZBXUBWUQSXUCFZXWLBXUBV
      XOSXUCFZXUEXWMXUKTVYIFXWOXULTXRVDBVYITWFQXVEBVXOCVYIUWMQBXUBESXUCFZXUSXWN
      XUKVWSXWPXULWLBEVYIUWHQZXVIBEVYRVYIYPQBWUPWUQVYIYPQBVYCWURTYQWHXUAXVMBXUB
      WUTSXUCFZXWBXUFXVNXVRXVAXWRXVSXVDBVXSVYNVYIYOQBVYAWUTTYSWHWUOWUSWVABTUWIW
      HWUHWVBBTYTQWVIBVYJKVYLFZWVNBVYJKVYLFZWYOWVFBVYJKVYLFZWVHBVYJKVYLFZXWSXUA
      BXUBWVDSXUCFZBXUBWVESXUCFZXXAXUFXWPXVGXXCXWQXVHBEVYQVYIYPQZXVRXUEXXDXVSXV
      EBVXSCVYIYOQBWVDWVETYSWHXUAXVMBXUBWVGSXUCFZXXBXUFXVNXWJXVGXXFXWKXVHBVXQVY
      QVYIYOQBVYAWVGTYSWHWVFWVHBTYTQWVLBVYJKVYLFZWVMBVYJKVYLFZXWTXUAXXCBXUBWVKS
      XUCFZXXGXUFXXEXWJBXUBWVJSXUCFZXXIXWKXUKEVYIFXXJXULCEUJHVYIEXVCVVTYKBVYIEW
      FQZBVXQWVJVYIYOQBWVDWVKTYSWHXUAXXJXVGXXHXUFXXKXVHBWVJVYQTUWJWHWVLWVMBTYTQ
      WVIWVNBTYTQWVCWVOBTYTQUWNVUQUBUDUFUCUAABTWMWNWOWPWQXEGUGUEYNXTYBYDYFYHYRU
      WOQUXIVURAGYTQVWRAVWTUXCSVXAFZVXHWCVVRVVQXXLVVSVWAAUXGEWFQZAUXCGWJQVUSVUT
      AGYTQVVBAUXHKVVHFZVVCAUXHKVVHFZVXFVWRVXKXXNWCVXMAUXBGUWPQVWRXXLXXOWCXXMAU
      XCGUWPQVVBVVCAGYTQVVAVVDAGUWQQUXAVVEAGYTQUWN $.
      $( [11-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    X and Y sequences 5: Diophantine representability of X, ^, _C
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A y $.  $d N y $.  $d X y $.
    $( X can be expressed in terms of Y, so it is also Diophantine. $)
    rmxdiophlem $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 /\ X e. NN0 ) -> ( X =
      ( A rmX N ) <-> E. y e. NN0 ( y = ( A rmY N ) /\ ( ( X ^ 2 ) - ( (
        ( A ^ 2 ) - 1 ) x. ( y ^ 2 ) ) ) = 1 ) ) ) $=
      ( c2 wcel cn0 co wceq cexp c1 cmin cmul wa cc nn0sscn nn0sqcl syl2anc syl
      wb cuz cfv w3a crmx crmy cv wrex 3ad2ant3 sseldi simp1 nn0z 3ad2ant2 frmx
      cz fovcl cn csquarenn cdif rmspecnonsq eldifi nnnn0 3syl 3ad2ant1 3adant3
      rmynn0 nn0mulcl subcan2 syl3anc rmxynorm eqeq2d cr cc0 cle wbr nn0ge0 jca
      nn0re sq11 3bitr3rd oveq1 oveq2d eqeq1d ceqsrexv bitr4d ) BEUAUBZFZCGFZDG
      FZUCZDBCUDHZIZDEJHZBEJHKLHZBCUEHZEJHZMHZLHZKIZAUFZWNIZWLWMWSEJHZMHZLHZKIZ
      NAGUGZWIWQWJEJHZWPLHZIZWLXFIZWRWKWIWLOFXFOFWPOFXHXITWIGOWLPWHWFWLGFWGDQUH
      UIWIGOXFPWIWJGFZXFGFWIWFCUNFZXJWFWGWHUJZWGWFXKWHCUKULZBCGWEUNUDUMUORZWJQS
      UIWIGOWPPWIWMGFZWOGFZWPGFWFWGXOWHWFWMUPUQURFWMUPFXOBUSWMUPUQUTWMVAVBVCWIW
      NGFZXPWFWGXQWHBCVEVDZWNQSWMWOVFRUIWLXFWPVGVHWIXGKWQWIWFXKXGKIXLXMBCVIRVJW
      IDVKFZVLDVMVNZNZWJVKFZVLWJVMVNZNZXIWKTWHWFYAWGWHXSXTDVQDVOVPUHWIXJYDXNXJY
      BYCWJVQWJVOVPSDWJVRRVSWIXQXEWRTXRXDWRAWNGWTXCWQKWTXBWPWLLWTXAWOWMMWSWNEJV
      TWAWAWBWCSWD $.
      $( [15-Oct-2014] $)
  $}

  ${
    $d a b c d $.
    $( X is a Diophantine function. $)
    rmxdioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( a ` 1 ) e. ( ZZ>= ` 2 )
        /\ ( a ` 3 ) = ( ( a ` 1 ) rmX ( a ` 2 ) ) ) } e. ( Dioph ` 3 ) $=
      ( vb vc c1 cfv c2 wcel c3 co wceq wa cn0 cfz crab crmy cexp cmin c4 mp2an
      cmpt cv cuz crmx cmap cmul wrex cdioph wb simpr wf nn0ex elmap biimpi 2nn
      ovex df-3 ssid jm2.27dlem5 jm2.27dlem3 sselii ffvelrn sylancl rmxdiophlem
      adantr 3nn syl3anc pm5.32da anass rexbii r19.42v bitr2i rabbiia wsbc cres
      syl6bb 3nn0 vex resex fvex 1nn jm2.27dlem1 eleq1d oveq12d eqeq12d anbi12d
      df-2 oveq1d oveq1 oveqan12d eqeq1d sbc2ie 4nn0 rmydioph simp1 simp3 simp2
      a1i w3a df-4 4nn rabren3dioph cmzp cvv mzpproj 2nn0 mzpexpmpt mzpconstmpt
      cz mzpsubmpt mzpmulmpt eqrabdioph mp3an anrabdioph eqeltri rexfrabdioph
      1z ) DAUAZEZFUBEZGZHXQEZXRFXQEZUCIJZKZALDHMIZUDIZNXTBUAZXRYBOIZJZKZYAFPIZ
      XRFPIZDQIZYGFPIZUEIZQIZDJZKZBLUFZAYFNZHUGEZYDYSAYFXQYFGZYDXTYIYQKZBLUFZKZ
      YSUUBXTYCUUDUUBXTKXTYBLGZYALGZYCUUDUHUUBXTUIUUBUUFXTUUBYELXQUJZFYEGUUFUUB
      UUHLYEXQUKDHMUOULUMZDFMIZYEFFHHUNUPYEUQURZFUNUSZUTZYELFXQVAVBVDUUBUUGXTUU
      BUUHHYEGUUGUUIHVEUSZYELHXQVAVBVDBXRYBYAVCVFVGYSXTUUCKZBLUFUUEYRUUOBLXTYIY
      QVHVIXTUUCBLVJVKVOVLHLGYRBRCUAZEZVMAUUPYEVNZVMZCLDRMIZUDIZNZRUGEZGYTUUAGV
      PUVBDUUPEZXSGZUUQUVDFUUPEZOIZJZKZHUUPEZFPIZUVDFPIZDQIZUUQFPIZUEIZQIZDJZKZ
      CUVANZUVCUUSUVRCUVAUUSUVRUHUUPUVAGYRUVRABUURUUQUUPYECVQVRRUUPVSXQUURJZYGU
      UQJZKZYJUVIYQUVQUWBXTUVEYIUVHUVTXTUVEUHUWAUVTXRUVDXSDHACDDMIZYEDDFHVTWFUU
      KURDVTUSZUTWAZWBVDUWBYGUUQYHUVGUVTUWAUIUVTYHUVGJUWAUVTXRUVDYBUVFOUWEFHACU
      UMWAWCVDWDWEUWBYPUVPDUWBYKUVKYOUVOQUVTYKUVKJUWAUVTYAUVJFPHHACUUNWAWGVDUVT
      UWAYMUVMYNUVNUEUVTYLUVLDQUVTXRUVDFPUWEWGWGYGUUQFPWHWIWCWJWEWKWQVLUVICUVAN
      UVCGZUVQCUVANUVCGZUVSUVCGRLGZDYGEZXSGZHYGEZUWIFYGEZOIZJZKZBYFNUUAGUWFWLBW
      MUWOUVIRDFRBCUWIUVDJZUWLUVFJZUWKUUQJZWRZUWJUVEUWNUVHUWSUWIUVDXSUWPUWQUWRW
      NZWBUWSUWKUUQUWMUVGUWPUWQUWRWOUWSUWIUVDUWLUVFOUWTUWPUWQUWRWPWCWDWEUWCUUTD
      DFRVTWFFHRUNUPHRRVEWSUUTUQURZURZURUWDUTZUUJUUTFUXBUULUTRWTUSZXASUWHCXHUUT
      UDIZUVPTUUTXBEZGZCUXEDTUXFGZUWGWLCUXEUVKTUXFGZCUXEUVOTUXFGZUXGCUXEUVJTUXF
      GZFLGZUXIUUTXCGZHUUTGUXKDRMUOZYEUUTHUXAUUNUTCUUTHXDSXECUVJFUUTXFSCUXEUVMT
      UXFGZCUXEUVNTUXFGZUXJCUXEUVLTUXFGZUXHUXOCUXEUVDTUXFGZUXLUXQUXMDUUTGUXRUXN
      UXCCUUTDXDSXECUVDFUUTXFSUXMDXHGUXHUXNXPCDUUTXGSZCUVLDUUTXISCUXEUUQTUXFGZU
      XLUXPUXMRUUTGUXTUXNUXDCUUTRXDSXECUUQFUUTXFSCUVMUVNUUTXJSCUVKUVOUUTXISUXSC
      UVPDRXKXLUVIUVQCRXMSXNYRBACRHWSXOSXN $.
      $( [17-Oct-2014] $)
  $}

  ${
    jm3.1.a $e |- ( ph -> A e. ( ZZ>= ` 2 ) ) $.
    jm3.1.b $e |- ( ph -> K e. ( ZZ>= ` 2 ) ) $.
    jm3.1.c $e |- ( ph -> N e. NN ) $.
    jm3.1.d $e |- ( ph -> ( K rmY ( N + 1 ) ) <_ A ) $.
    $( Lemma for ~ jm3.1 . $)
    jm3.1lem1 $p |- ( ph -> ( K ^ N ) < A ) $=
      ( co c2 c1 cmin cr wcel syl cn syl2anc cz clt wbr cexp cmul cn0 cuz nnnn0
      cfv eluzelre reexpcl 2z uzid ax-mp uz2mulcl sylancr uz2m1nn nnre cc0 3syl
      nngt0 cc wceq 2cn recnd mulcl ax-1cn a1i sub32 syl3anc caddc 2times pncan
      oveq1d eqtrd breqtrrd wb posdif mpbird crp eluz2b2 simplbi nnrp rpexpmord
      mpbid crmy nnz peano2zdi frmy fovcl zre cle jm2.17a letrd ltletrd ) ACDUA
      IZJCUBIZKLIZDUAIZBACMNZDUCNZWMMNACJUDUFZNZWQFJCUGOZADPNZWRGDUEOZCDUHQAWOM
      NZWRWPMNAWOPNZXDAWNWSNZXEAJWSNZWTXFJRNXGUIJUJUKFJCULUMWNUNOZWOUOOZXCWODUH
      QZABWSNBMNEJBUGOZACWOSTZWMWPSTZAXLUPWOCLIZSTZAUPCKLIZXNSAWTXPPNUPXPSTFCUN
      XPURUQAXNWNCLIZKLIZXPAWNUSNZKUSNZCUSNZXNXRUTAJUSNYAXSVAACXAVBZJCVCUMXTAVD
      VEYBWNKCVFVGAXQCKLAXQCCVHIZCLIZCAWNYCCLAYAWNYCUTYBCVIOVKAYAYAYDCUTYBYBCCV
      JQVLVKVLVMAWQXDXLXOVNXAXICWOVOQVPAXBCVQNZWOVQNZXLXMVNGAWTCPNZYEFWTYGKCSTC
      VRVSCVTUQAXEYFXHWOVTOCWODWAVGWBAWPCDKVHIZWCIZBXJAYIRNZYIMNAWTYHRNYJFADAXB
      DRNGDWDOWECYHRWSRWCWFWGQYIWHOXKAWTWRWPYIWITFXCCDWJQHWKWL $.
      $( [16-Oct-2014] $)

    $( Lemma for ~ jm3.1 . $)
    jm3.1lem2 $p |- ( ph -> ( K ^ N ) < ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) -
        1 ) ) $=
      ( co c2 cmin c1 cr wcel syl syl2anc caddc wbr cc wceq cexp cn0 cuz cfv cn
      cmul eluzelre nnnn0 reexpcl 2re remulcl sylancr resubcl sylancl jm3.1lem1
      resqcl 1re readdcl clt cz eluz2b1 simprbi eluz2b2 simplbi nngt0 ltmulgt11
      cc0 wb syl3anc mpbid crp uz2m1nn nnrp 3syl ltaddrp lttrd recnd exp1 nnge1
      cle syl6eleq expwordi eqbrtrrd lelttrd eluzelz zltp1le peano2re syl112anc
      nnuz lemul1 leadd1 ax-1cn a1i addsub12 adddir sqval oveq12d pncan2 mulid2
      mulcl 3eqtrd oveq1d oveq2d subadd23 3eqtr3d 2cn mulass 2times eqtrd sub32
      addsubass 3brtr4d ltletrd ) ACDUAIZBJBUFIZCUFIZCJUAIZKIZLKIZACMNZDUBNZXNM
      NACJUCUDZNZXTFJCUGOZADUENYAGDUHOCDUIPZABYBNZBMNZEJBUGOZAXRMNZLMNZXSMNAXPM
      NZXQMNZYIAXOMNZXTYKAJMNYGYMUJYHJBUKULYDXOCUKPAXTYLYDCUPOZXPXQUMPUQXRLUMUN
      ZABCDEFGHUOZABBCUFIZCLKIZQIZXSYHAYQMNZYRMNZYSMNAYGXTYTYHYDBCUKPZAXTYJUUAY
      DUQCLUMUNYQYRURPZYOABYQYSYHUUBUUCALCUSRZBYQUSRZAYCUUDFYCCUTNZUUDCVAVBOAYG
      XTVGBUSRZUUDUUEVHYHYDABUENZUUGAYFUUHEYFUUHLBUSRBVCVDOBVEOBCVFVIVJAYTYRVKN
      ZYQYSUSRUUBAYCYRUENUUIFCVLYRVMVNYQYRVOPVPACLQIZCUFIZYQLKIZXQKIZQIZYQUUMQI
      ZYSXSVTAUUKYQVTRZUUNUUOVTRZAUUJBVTRZUUPACBUSRZUURACXNBYDYEYHACLUAIZCXNVTA
      CSNZUUTCTACYDVQZCVROAXTLCVTRZDLUCUDZNUUTXNVTRYDACUENZUVCAYCUVEFYCUVEUUDCV
      CVDOZCVSOADUEUVDGWIWACLDWBVIWCYPWDAUUFBUTNZUUSUURVHAYCUUFFJCWEOAYFUVGEJBW
      EOCBWFPVJAUUJMNZYGXTVGCUSRZUURUUPVHAXTUVHYDCWGOZYHYDAUVEUVIUVFCVEOUUJBCWJ
      WHVJAUUKMNZYTUUMMNZUUPUUQVHAUVHXTUVKUVJYDUUJCUKPZUUBAUULMNZYLUVLAYTYJUVNU
      UBUQYQLUMUNZYNUULXQUMPUUKYQUUMWKVIVJAYQUUKXQKIZLKIZQIZUVPUULQIZYSUUNAYQSN
      ZUVPSNLSNZUVRUVSTAYQUUBVQZAUVPAUVKYLUVPMNUVMYNUUKXQUMPVQUWAAWLWMZYQUVPLWN
      VIAUVQYRYQQAUVPCLKAUVPCCUFIZLCUFIZQIZUWDKIZUWECAUUKUWFXQUWDKAUVAUWAUVAUUK
      UWFTUVBUWCUVBCLCWOVIAUVAXQUWDTUVBCWPOWQAUWDSNZUWESNZUWGUWETAUVAUVAUWHUVBU
      VBCCWTPAUWAUVAUWIWLUVBLCWTULUWDUWEWRPAUVAUWECTUVBCWSOXAXBXCAUUKSNXQSNZUUL
      SNZUVSUUNTAUUKUVMVQAXQYNVQZAUULUVOVQZUUKXQUULXDVIXEAXSYQYQQIZXQKIZLKIZUWN
      LKIZXQKIZUUOAXRUWOLKAXPUWNXQKAXPJYQUFIZUWNAJSNZBSNUVAXPUWSTUWTAXFWMABYHVQ
      UVBJBCXGVIAUVTUWSUWNTUWBYQXHOXIXBXBAUWNSNUWJUWAUWPUWRTAUWNAYTYTUWNMNUUBUU
      BYQYQURPVQUWLUWCUWNXQLXJVIAUWRYQUULQIZXQKIZUUOAUWQUXAXQKAUVTUVTUWAUWQUXAT
      UWBUWBUWCYQYQLXKVIXBAUVTUWKUWJUXBUUOTUWBUWMUWLYQUULXQXKVIXIXAXLXMVP $.
      $( [16-Oct-2014] $)

    $( Lemma for ~ jm3.1 . $)
    jm3.1lem3 $p |- ( ph -> ( ( ( ( 2 x. A ) x. K ) -
        ( K ^ 2 ) ) - 1 ) e. NN ) $=
      ( c2 cmul co cz wcel cc0 clt wbr cn syl syl2anc cr cexp c1 2z cuz eluzelz
      cmin cfv zmulcl sylancr eluz2b2 simplbi nnz zsqcl zsubcl peano2zm 0re a1i
      cn0 nnnn0 nnexpcl nnre zre nngt0 jm3.1lem2 lttrd elnnz sylanbrc ) AIBJKZC
      JKZCIUAKZUFKZUBUFKZLMZNVLOPVLQMAVKLMZVMAVILMZVJLMZVNAVHLMZCLMZVOAILMBLMZV
      QUCABIUDUGZMVSEIBUERIBUHUIACQMZVRACVTMZWAFWBWAUBCOPCUJUKRZCULRZVHCUHSAVRV
      PWDCUMRVIVJUNSVKUORZANCDUAKZVLNTMAUPUQAWFQMZWFTMAWADURMZWGWCADQMWHGDUSRCD
      UTSZWFVARAVMVLTMWEVLVBRAWGNWFOPWIWFVCRABCDEFGHVDVEVLVFVG $.
      $( [17-Oct-2014] $)
  $}

  ${
    $d A a $.  $d K a $.  $d N a $.
    $( Diophantine expression for exponentiation.  Lemma 3.1 of
       [JonesMatijasevic]. $)
    jm3.1 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ K e. ( ZZ>= ` 2 ) /\ N e. NN ) /\
        ( K rmY ( N + 1 ) ) <_ A ) -> ( K ^ N ) = ( ( ( A rmX N ) - ( ( A - K )
          x. ( A rmY N ) ) ) mod ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) -
          1 ) ) ) $=
      ( c2 wcel cn c1 co crmy wbr wa cexp crmx cmin cmul cz cn0 3ad2ant3 adantr
      syl2anc cuz cfv w3a caddc cle cmo wceq clt cdivides wb simp1 nnz jca frmx
      fovcl nn0z 3syl eluzelz zsubcl syl2an 3adant3 zmulcl simpl1 simpl2 simpl3
      frmy syl simpr jm3.1lem3 2nn0 eluznn0 3ad2ant2 nnnn0 nn0expcl divalgmodcl
      mpan syl3anc jm3.1lem2 jm2.18 mpbir2and ) ADUAUBZEZBWAEZCFEZUCZBCGUDHIHAU
      EJZKZBCLHZACMHZABNHZACIHZOHZNHZDAOHBOHBDLHNHGNHZUFHUGZWHWNUHJZWNWMWHNHUIJ
      ZWGWMPEZWNFEWHQEZWOWPWQKUJWEWRWFWEWIPEZWLPEZWRWEWBCPEZKZWIQEWTWEWBXBWBWCW
      DUKWDWBXBWCCULRUMZACQWAPMUNUOWIUPUQWEWJPEZWKPEZXAWBWCXEWDWBAPEBPEXEWCDAUR
      DBURABUSUTVAWEXCXFXDACPWAPIVFUOVGWJWKVBTWIWLUSTSWGABCWBWCWDWFVCZWBWCWDWFV
      DZWBWCWDWFVEZWEWFVHZVIWEWSWFWEBQEZCQEZWSWCWBXKWDDQEWCXKVJBDVKVPVLZWDWBXLW
      CCVMZRBCVNTSWNWHWMVOVQWGABCXGXHXIXJVRWGWBXKXLWQXGWEXKWFXMSWGWDXLXIXNVGABC
      VSVQVT $.
      $( [16-Oct-2014] $)
  $}

  ${
    $d A d e f $.  $d B d e f $.  $d C d e f $.
    $( Lemma for ~ expdioph .  Fully expanded expression for exponential. $)
    expdiophlem1 $p |- ( C e. NN0 -> ( ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN ) /\ C
        = ( A ^ B ) ) <-> E. d e. NN0 E. e e. NN0 E. f e. NN0 ( ( A e. ( ZZ>= `
        2 ) /\ B e. NN ) /\ ( ( A e. ( ZZ>= ` 2 ) /\ d = ( A rmY ( B + 1 ) ) )
        /\ ( ( d e. ( ZZ>= ` 2 ) /\ e = ( d rmY B ) ) /\ ( ( d e. ( ZZ>= ` 2 )
        /\ f = ( d rmX B ) ) /\ ( C < ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1
        ) /\ ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1 ) || ( ( f - ( ( d - A )
        x. e ) ) - C ) ) ) ) ) ) ) ) $=
      ( cn0 wcel c2 wa co wceq c1 cmul cmin wbr cdivides wrex syl cz cuz cfv cn
      cexp cv caddc crmy crmx clt cmo cle cr 2re nnre peano2re adantl peano2zdi
      a1i nnz frmy fovcl sylan2 zre elnnuz eluzp1p1 df-2 fveq2i syl6eleqr sylbi
      eluzle nnnn0 peano2nn0 rmygeid letrd wb eluz sylancr mpbird simprl simprr
      leid jm3.1 syl31anc eqeq2d frmx syl2anc nn0z eluzelz adantr zsubcl zmulcl
      2z jm3.1lem3 simpl divalgmodcl syl3anc rmynn0 oveq1 oveq1d breq2d breq12d
      oveq2 oveq2d anbi12d rexbidv ceqsrexv anbi2d 3bitrrd r19.42v anbi2i bitri
      ad2antll rexbii syl6bbr eleq1 syl5ibrcom imp ibar pm5.32da ad2antrl bitrd
      anbi1d 2rexbidv 3bitrd 2rexbii 3bitri ) CGHZAIUAUBZHZBUCHZJZCABUDKZLZJYKY
      IFUEZABMUFKZUGKZLZJZYNYHHZDUEZYNBUGKZLZJZYSEUEZYNBUHKZLZJZCIYNNKZANKZAIUD
      KZOKZMOKZUIPZUULUUDYNAOKZYTNKZOKZCOKZQPZJZJZJZJZEGRZDGRZFGRZJZYKUVBJEGRZD
      GRFGRZYGYKYMUVEYGYKJZYMCYPBUHKZYPAOKZYPBUGKZNKZOKZIYPNKZANKZUUJOKZMOKZUJK
      ZLZCUVRUIPZUVRUVNCOKZQPZJZUVEUVIYLUVSCUVIYPYHHZYIYJYPYPUKPZYLUVSLYKUWEYGY
      KUWEIYPUKPZYKIYOYPIULHYKUMURYJYOULHZYIYJBULHUWHBUNBUOSUPYKYPTHZYPULHZYJYI
      YOTHUWIYJBBUSZUQAYOTYHTUGUTVAVBZYPVCSZYJIYOUKPZYIYJYOYHHZUWNYJBMUAUBHZUWO
      BVDUWPYOMMUFKZUAUBYHMBVEIUWQUAVFVGVHVIIYOVJSUPYJYIYOGHZYOYPUKPYJBGHZUWRBV
      KZBVLSZAYOVMVBVNYKITHUWIUWEUWGVOWLUWLIYPVPVQVRZUPZYGYIYJVSZYGYIYJVTZYKUWF
      YGYKUWJUWFUWMYPWASUPZYPABWBWCWDUVIUVNTHZUVRUCHYGUVTUWDVOYKUXGYGYKUVJTHZUV
      MTHZUXGYKUVJGHZUXHYKUWEBTHZUXJUXBYJUXKYIUWKUPZYPBGYHTUHWEVAZWFUVJWGSYKUVK
      THZUVLTHZUXIYKUWIATHZUXNUWLYIUXPYJIAWHWIYPAWJWFYKUWEUXKUXOUXBUXLYPBTYHTUG
      UTVAWFUVKUVLWKWFUVJUVMWJWFUPUVIYPABUXCUXDUXEUXFWMYGYKWNUVRCUVNWOWPUVIUWDY
      QUUBUUFUUSJZJZJZEGRZDGRZFGRZUVEUVIUWDYQUUBUXQEGRZJZDGRZJZFGRZUYBUVIUYGYTU
      VLLZUUDUVJLZUWAUVRUUDUVKYTNKZOKZCOKZQPZJZJZEGRZJZDGRZUYIUWAUVRUUDUVMOKZCO
      KZQPZJZJZEGRZUWDUVIYPGHZUYGUYRVOYKVUEYGYJYIUWRVUEUXAAYOWQVBUPUYEUYRFYPGYQ
      UYDUYQDGYQUUBUYHUYCUYPYQUUAUVLYTYNYPBUGWRWDYQUXQUYOEGYQUUFUYIUUSUYNYQUUEU
      VJUUDYNYPBUHWRWDYQUUMUWAUURUYMYQUULUVRCUIYQUUKUVQMOYQUUIUVPUUJOYQUUHUVOAN
      YNYPINXBWSWSWSZWTYQUULUVRUUQUYLQVUFYQUUPUYKCOYQUUOUYJUUDOYQUUNUVKYTNYNYPA
      OWRWSXCWSXAXDXDXEXDXEXFSUVIUVLGHZUYRVUDVOUVIUWEUWSVUGUXCYJUWSYGYIUWTXLYPB
      WQWFUYPVUDDUVLGUYHUYOVUCEGUYHUYNVUBUYIUYHUYMVUAUWAUYHUYLUYTUVRQUYHUYKUYSC
      OUYHUYJUVMUUDOYTUVLUVKNXBXCWSWTXGXGXEXFSUVIUXJVUDUWDVOUVIUWEUXKUXJUXCYJUX
      KYGYIUWKXLUXMWFVUBUWDEUVJGUYIVUAUWCUWAUYIUYTUWBUVRQUYIUYSUVNCOUUDUVJUVMOW
      RWSWTXGXFSXHUYAUYFFGUYAYQUYDJZDGRUYFUXTVUHDGUXTYQUXREGRZJVUHYQUXREGXIVUIU
      YDYQUUBUXQEGXIXJXKXMYQUYDDGXIXKXMXNUVIUXTUVCFDGGUVIUXSUVBEGUVIUXSYQUVAJUV
      BUVIYQUXRUVAUVIYQJYSUXRUVAVOUVIYQYSUVIYSYQUWEUXCYNYPYHXOXPXQYSUUBUUCUXQUU
      TYSUUBXRYSUUFUUGUUSYSUUFXRYBXDSXSUVIYQYRUVAYIYQYRVOYGYJYIYQXRXTYBYAXEYCYA
      YDXSUVHYKUVCJZDGRZFGRYKUVDJZFGRUVFUVGVUJFDGGYKUVBEGXIYEVUKVULFGYKUVCDGXIX
      MYKUVDFGXIYFXN $.
      $( [17-Oct-2014] $)
  $}

  ${
    $d a b c d e f $.

    $( Lemma for ~ expdioph .  Exponentiation on a restricted domain is
       Diophantine. $)
    expdiophlem2 $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( ( a ` 1 ) e. ( ZZ>=
        ` 2 ) /\ ( a ` 2 ) e. NN ) /\ ( a ` 3 ) = ( ( a ` 1 ) ^ ( a ` 2 ) ) ) }
        e. ( Dioph ` 3 ) $=
      ( vb ve c1 cfv c2 wcel wa c3 co wceq cn0 crab cmin c6 c4 anbi12d mp2an c7
      cmpt vc vd cv cuz cn cexp cfz cmap caddc crmy crmx cmul clt cdivides wrex
      wbr cdioph wb wf nn0ex ovex elmap biimpi jm2.27dlem3 ffvelrn expdiophlem1
      3nn sylancl syl rabbiia wsbc cres 3nn0 vex resex fvex eqeq1 anbi2d adantr
      adantl simpr oveq2 oveq12d oveq1d breq2d sbc2ie sbcbiii 1nn df-2 2nn df-3
      c5 ssid jm2.27dlem5 sselii jm2.27dlem1 eleq1d eqeqan12rd eleq1 oveqan12rd
      jm2.27dlem2 id eqeq2d breq12d oveq2d bitri a1i cz cmzp 6nn nnnn0i 2z df-4
      cvv 4nn df-5 mzpproj eluzrabdioph mp3an elnnrabdioph anrabdioph peano2nn0
      5nn df-6 ceqsrexv 3syl eqeq12d 7nn df-7 1z mzpconstmpt rmydioph w3a simp1
      simp3 simp2 rabren3dioph eqeltri mzpmulmpt mzpsubmpt oveqan12d eqrabdioph
      bicomd mzpaddmpt rexfrabdioph rmxdioph mzpexpmpt ltrabdioph 3rexfrabdioph
      2nn0 dvdsrabdioph ) DAUCZEZFUDEZGZFUULEZUEGZHZIUULEZUUMUUPUFJKHZALDIUGJZU
      HJZMUURUUOBUCZUUMUUPDUIJZUJJZKZHZUVCUUNGZUAUCZUVCUUPUJJZKZHZUVHUBUCZUVCUU
      PUKJZKZHZUUSFUVCULJZUUMULJZUUMFUFJZNJZDNJZUMUPZUWAUVMUVCUUMNJZUVIULJZNJZU
      USNJZUNUPZHZHZHZHZHZUBLUOUALUOBLUOZAUVBMZIUQEZUUTUWMAUVBUULUVBGZUUSLGZUUT
      UWMURUWPUVALUULUSZIUVAGUWQUWPUWRLUVAUULUTDIUGVAVBVCIVGVDZUVALIUULVEVHUUMU
      UPUUSUAUBBVFVIVJILGUWLUBOCUCZEZVKUAWLUWTEZVKZBPUWTEZVKZAUWTUVAVLZVKZCLDOU
      GJZUHJZMZOUQEZGUWNUWOGVMUXJDUWTEZUUNGZFUWTEZUEGZHZUXMUXDUXLUXNDUIJZUJJZKZ
      HZUXDUUNGZUXBUXDUXNUJJZKZHZUYAUXAUXDUXNUKJZKZHZIUWTEZFUXDULJZUXLULJZUXLFU
      FJZNJZDNJZUMUPZUYMUXAUXDUXLNJZUXBULJZNJZUYHNJZUNUPZHZHZHZHZHZCUXIMZUXKUXG
      VUDCUXIUXGVUDURUWTUXIGZUXGUURUVGUVHUXBUVJKZHZUVHUXAUVNKZHZUWBUWAUXAUWCUXB
      ULJZNJZUUSNJZUNUPZHZHZHZHZHZBUXDVKZAUXFVKVUDUXEVUTUXFAUWTUVACVNVOZUXCVUSU
      XDBPUWTVPZUWLVUSUAUBUXBUXAWLUWTVPOUWTVPUVIUXBKZUVMUXAKZHZUWKVURUURVVEUWJV
      UQUVGVVEUVLVUHUWIVUPVVCUVLVUHURVVDVVCUVKVUGUVHUVIUXBUVJVQVRVSVVEUVPVUJUWH
      VUOVVDUVPVUJURVVCVVDUVOVUIUVHUVMUXAUVNVQVRVTVVEUWGVUNUWBVVEUWFVUMUWAUNVVE
      UWEVULUUSNVVEUVMUXAUWDVUKNVVCVVDWAVVCUWDVUKKVVDUVIUXBUWCULWBVSWCWDWEVRQQV
      RVRWFWGWGVUSVUDABUXFUXDVVAVVBUULUXFKZUVCUXDKZHZUURUXPVURVUCVVFUURUXPURVVG
      VVFUUOUXMUUQUXOVVFUUMUXLUUNDIACDDUGJZUVADDFIWHWIFIIWJWKUVAWMWNWNDWHVDZWOW
      PZWQZVVFUUPUXNUEFIACFFIFWJVDZWKWJXAWPZWQQVSVVHUVGUXTVUQVUBVVHUUOUXMUVFUXS
      VVFUUOUXMURVVGVVLVSVVGVVFUVCUXDUVEUXRVVGXBZVVFUUMUXLUVDUXQUJVVKVVFUUPUXND
      UIVVNWDWCWRQVVHVUHUYDVUPVUAVVHUVHUYAVUGUYCVVGUVHUYAURVVFUVCUXDUUNWSVTZVVH
      UVJUYBUXBVVGVVFUVCUXDUUPUXNUJVVOVVNWTXCQVVHVUJUYGVUOUYTVVHUVHUYAVUIUYFVVP
      VVHUVNUYEUXAVVGVVFUVCUXDUUPUXNUKVVOVVNWTXCQVVHUWBUYNVUNUYSVVHUUSUYHUWAUYM
      UMVVFUUSUYHKVVGIIACUWSWPVSZVVHUVTUYLDNVVHUVRUYJUVSUYKNVVGVVFUVQUYIUUMUXLU
      LUVCUXDFULWBVVKWTVVFUVSUYKKVVGVVFUUMUXLFUFVVKWDVSWCWDZXDVVHUWAUYMVUMUYRUN
      VVRVVHVULUYQUUSUYHNVVHVUKUYPUXANVVHUWCUYOUXBULVVHUVCUXDUUMUXLNVVFVVGWAVVF
      UUMUXLKVVGVVKVSWCWDXEVVQWCXDQQQQQWFXFXGVJUXPCUXIMUXKGZVUCCUXIMUXKGZVUEUXK
      GUXMCUXIMUXKGZUXOCUXIMUXKGZVVSOLGZFXHGZCXHUXHUHJZUXLTUXHXIEZGZVWAOXJXKZXL
      UXHXNGZDUXHGVWGDOUGVAZVVIUXHDDFOWHWIFIOWJWKIPOVGXMPWLOXOXPWLOOYCYDUXHWMWN
      WNZWNZWNZWNVVJWOZCUXHDXQRZCUXLFOXRXSVWCCVWEUXNTVWFGZVWBVWHVWIFUXHGZVWPVWJ
      DFUGJUXHFVWMVVMWOZCUXHFXQRCUXNOXTRUXMUXOCOYARUXTCUXIMZUXKGVUBCUXIMUXKGZVV
      TVWSUVCUXQKZUXMUXDUXLUVCUJJZKZHZHZBLUOZCUXIMZUXKUXTVXFCUXIVUFVXFUXTVUFUXN
      LGZUXQLGVXFUXTURVUFUXHLUWTUSZVWQVXHVUFVXILUXHUWTUTVWJVBVCVWRUXHLFUWTVEVHU
      XNYBVXDUXTBUXQLVXAVXCUXSUXMVXAVXBUXRUXDUVCUXQUXLUJWBXCVRYEYFUUCVJVWCVXEBS
      UULEZVKCUULUXHVLZVKZALDSUGJZUHJZMZSUQEZGVXGUXKGVWHVXOVXJUVDKZUUOPUULEZUUM
      VXJUJJZKZHZHZAVXNMZVXPVXLVYBAVXNVXLVYBURUULVXNGVXEVYBCBVXKVXJUULUXHAVNVOS
      UULVPUWTVXKKZUVCVXJKZHZVXAVXQVXDVYAVYEVYDUVCVXJUXQUVDVYEXBZVYDUXNUUPDUIFO
      CAVWRWPWDWRVYFUXMUUOVXCVXTVYFUXLUUMUUNVYDUXLUUMKVYEDOCAVWNWPZVSWQVYFUXDVX
      RVXBVXSVYDUXDVXRKVYEPOCADPUGJUXHPVWKPXOVDWOZWPVSVYDVYEUXLUUMUVCVXJUJVYHVY
      GUUAYGQQWFXGVJVXQAVXNMVXPGZVYAAVXNMVXPGZVYCVXPGSLGZAXHVXMUHJZVXJTVXMXIEZG
      ZAVYMUVDTVYNGZVYJSYHXKZVXMXNGZSVXMGVYODSUGVAZSYHVDZAVXMSXQRAVYMUUPTVYNGZA
      VYMDTVYNGZVYPVYRFVXMGWUAVYSFOSVWRYIXJXAAVXMFXQRVYRDXHGZWUBVYSYJADVXMYKRAU
      UPDVXMUUDRAVXJUVDSUUBXSVYLDUVCEZUUNGZIUVCEZWUDFUVCEZUJJZKZHZBUVBMUWOGVYKV
      YQBYLWUJVYASDSPBAWUDUUMKZWUGVXJKZWUFVXRKZYMZWUEUUOWUIVXTWUNWUDUUMUUNWUKWU
      LWUMYNZWQWUNWUFVXRWUHVXSWUKWULWUMYOWUNWUDUUMWUGVXJUJWUOWUKWULWUMYPWCYGQDO
      SVWNYIXJXAVYTPOSVYIYIXJXAYQRVXQVYAASYARYRVXEBCASOYIUUERYRUYDCUXIMUXKGZVUA
      CUXIMUXKGZVWTVWCUUOUUSUUMUUPUJJZKZHZAUVBMUWOGWUPVWHAYLWUTUYDOPFWLACUUMUXD
      KZUUPUXNKZUUSUXBKZYMZUUOUYAWUSUYCWVDUUMUXDUUNWVAWVBWVCYNZWQWVDUUSUXBWURUY
      BWVAWVBWVCYOWVDUUMUXDUUPUXNUJWVEWVAWVBWVCYPWCYGQVYIVWRWLWLOWLYCVDYDYCXAZY
      QRUYGCUXIMUXKGZUYTCUXIMUXKGZWUQVWCUUOUUSUUMUUPUKJZKZHZAUVBMUWOGWVGVWHAUUF
      WVKUYGOPFOACWVAWVBUUSUXAKZYMZUUOUYAWVJUYFWVMUUMUXDUUNWVAWVBWVLYNZWQWVMUUS
      UXAWVIUYEWVAWVBWVLYOWVMUUMUXDUUPUXNUKWVNWVAWVBWVLYPWCYGQVYIVWROXJVDZYQRUY
      NCUXIMUXKGZUYSCUXIMUXKGZWVHVWCCVWEUYHTVWFGZCVWEUYMTVWFGZWVPVWHVWIIUXHGWVR
      VWJUVAUXHIVWLUWSWOCUXHIXQRZCVWEUYLTVWFGZCVWEDTVWFGZWVSCVWEUYJTVWFGZCVWEUY
      KTVWFGZWWACVWEUYITVWFGZVWGWWCCVWEFTVWFGZCVWEUXDTVWFGZWWEVWIVWDWWFVWJXLCFU
      XHYKRVWIPUXHGWWGVWJVYICUXHPXQRZCFUXDUXHYSRVWOCUYIUXLUXHYSRVWGFLGWWDVWOUUJ
      CUXLFUXHUUGRCUYJUYKUXHYTRVWIWUCWWBVWJYJCDUXHYKRCUYLDUXHYTRZCUYHUYMOUUHXSV
      WCWVSCVWEUYRTVWFGZWVQVWHWWICVWEUYQTVWFGZWVRWWJCVWEUXATVWFGZCVWEUYPTVWFGZW
      WKVWIOUXHGWWLVWJWVOCUXHOXQRCVWEUYOTVWFGZCVWEUXBTVWFGZWWMWWGVWGWWNWWHVWOCU
      XDUXLUXHYTRVWIWLUXHGWWOVWJWVFCUXHWLXQRCUYOUXBUXHYSRCUXAUYPUXHYTRWVTCUYQUY
      HUXHYTRCUYMUYROUUKXSUYNUYSCOYARUYGUYTCOYARUYDVUACOYARUXTVUBCOYARUXPVUCCOY
      ARYRUWLUBUABACOWLPIXMXPYDUUIRYR $.
      $( [17-Oct-2014] $)

    $( The exponential function is Diophantine.  This result completes and
       encapsulates our development using Pell equation solution sequences and
       is sometimes regarded as Matiyasevich's theorem properly. $)
    expdioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( a ` 3 ) = ( ( a ` 1 ) ^ (
        a ` 2 ) ) } e. ( Dioph ` 3 ) $=
      ( c3 cfv c1 c2 cexp co wceq cn0 cfz crab cn wcel wa wo cc0 wb eqeq2d 3nn0
      mp2an cv cmap cuz cdioph wn pm4.42 ancom nn0ex ovex elmap biimpi 1nn df-2
      2nn df-3 ssid jm2.27dlem5 jm2.27dlem3 sselii ffvelrn sylancl adantr elnn0
      wf elnn1uz2 orim1i 3syl biantrurd andir orbi1i bitri cz 1exp adantl oveq1
      nnz syl bibi1d syl5ibrcom pm5.32d iba anbi1d orbi12d 0exp syl5bb pm5.32da
      bitrd wi pm2.53 sylbi 0nnn eleq1 impbid1 cc nn0cn exp0 oveq2 rabbiia cmpt
      mtbiri cmzp cvv mzpproj elnnrabdioph 1z mzpconstmpt eqrabdioph anrabdioph
      mp3an 3nn expdiophlem2 orrabdioph eq0rabdioph eqeltri ) BAUAZCZDXOCZEXOCZ
      FGZHZAIDBJGZUBGZKXRLMZXQDHZXPDHZNZXQEUCCMZYCNZXTNZOZXQPHZXPPHZNZOZNZXRPHZ
      YENZOZAYBKZBUDCZXTYRAYBXTXTYCNZXTYCUEZNZOXOYBMZYRXTYCUFUUDUUAYOUUCYQUUAYC
      XTNUUDYOXTYCUGUUDYCXTYNUUDYCNZXTYDYGOZYKOZXTNZYNUUEUUGXTUUEXQIMZXQLMZYKOZ
      UUGUUDUUIYCUUDYAIXOVDZDYAMZUUIUUDUULIYAXOUHDBJUIZUJUKZDDJGYADDEBULUMEBBUN
      UOYAUPUQZUQDULURUSZYAIDXOUTVAZVBUUIUUKXQVCUKUUJUUFYKUUJUUFXQVEUKVFVGVHUUH
      YDXTNZYGXTNZOZYKXTNZOZUUEYNUUHUUFXTNZUVBOUVCUUFYKXTVIUVDUVAUVBYDYGXTVIVJV
      KUUEUVAYJUVBYMUUEUUSYFUUTYIUUEYDXTYEUUEXTYEQZYDXPDXRFGZHZYEQUUEUVFDXPYCUV
      FDHZUUDYCXRVLMUVHXRVPXRVMVQVNRYDXTUVGYEYDXSUVFXPXQDXRFVORVRVSVTUUEYGYHXTY
      CYGYHQUUDYCYGWAVNWBWCUUEYKXTYLUUEXTYLQYKXPPXRFGZHZYLQUUEUVIPXPYCUVIPHUUDX
      RWDVNRYKXTUVJYLYKXSUVIXPXQPXRFVORVRVSVTWCWEWGWFWEUUCUUBXTNZUUDYQXTUUBUGUU
      DUVKYPXTNYQUUDUUBYPXTUUDXRIMZUUBYPQUUDUULEYAMZUVLUUODEJGYAEUUPEUNURUSZYAI
      EXOUTVAUVLUUBYPUVLYCYPOUUBYPWHXRVCYCYPWIWJYPYCPLMWKXRPLWLWTWMVQWBUUDYPXTY
      EUUDUVEYPXPXQPFGZHZYEQUUDUVODXPUUDUUIXQWNMUVODHUURXQWOXQWPVGRYPXTUVPYEYPX
      SUVOXPXRPXQFWQRVRVSVTWGWEWCWEWRYOAYBKYTMZYQAYBKYTMZYSYTMYCAYBKYTMZYNAYBKY
      TMZUVQBIMZAVLYAUBGZXRWSYAXACZMZUVSSYAXBMZUVMUWDUUNUVNAYAEXCTZAXRBXDTYJAYB
      KYTMZYMAYBKYTMZUVTYFAYBKYTMZYIAYBKYTMUWGYDAYBKYTMZYEAYBKYTMZUWIUWAAUWBXQW
      SUWCMZAUWBDWSUWCMZUWJSUWEUUMUWLUUNUUQAYADXCTZUWEDVLMUWMUUNXEADYAXFTZAXQDB
      XGXIUWAAUWBXPWSUWCMZUWMUWKSUWEBYAMUWPUUNBXJURAYABXCTZUWOAXPDBXGXIZYDYEABX
      HTAXKYFYIABXLTYKAYBKYTMZYLAYBKYTMZUWHUWAUWLUWSSUWNAXQBXMTUWAUWPUWTSUWQAXP
      BXMTYKYLABXHTYJYMABXLTYCYNABXHTYPAYBKYTMZUWKUVRUWAUWDUXASUWFAXRBXMTUWRYPY
      EABXHTYOYQABXLTXN $.
      $( [17-Oct-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Uncategorized stuff not associated with a major project
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d x y B $.
    $( Epsilon induction for sets contained in a transitive set.  If we are
       allowed to assume Infinity, then all sets have a transitive closure and
       this reduces to ~ setind ; however, this version is useful without
       Infinity. $)
    setindtr $p |- ( A. x ( x C_ A -> x e. A ) -> ( E. y ( Tr y /\ B e. y ) ->
        B e. A ) ) $=
      ( cv wtr wcel wa wex wss wi wal cdif c0 wceq cin wn sylib adantlr ex wrex
      wral ax-17 hba1 hban eldifn adantl wel eldifi trss syl5 df-ss sseq1d ax-4
      imp ad2antlr sylbid mtod inssdif0 sylnib ralrimi ralnex difss ssexi zfreg
      vex necon1bi syl ssdif0 sylibr simplr sseldd exlimiv com12 ) BEZFZDVOGZHZ
      BIAEZCJZVSCGZKZALZDCGZVRWCWDKBVRWCWDVRWCHVOCDVPWCVOCJZVQVPWCHZVOCMZNOZWEW
      FVSWGPNOZAWGUAZQZWHWFWIQZAWGUBWKWFWLAWGVPWCAVPAUCWBAUDUEWFVSWGGZWLWFWMHZV
      SVOPZCJZWIWNWPWAWMWAQWFVSVOCUFUGWNWPVTWAWNWOVSCVPWMWOVSOZWCVPWMHVSVOJZWQV
      PWMWRWMABUHVPWRVSVOCUIVOVSUJUKUOVSVOULRSUMWCWBVPWMWBAUNUPUQURVSVOCUSUTTVA
      WIAWGVBRWJWGNAWGWGVOBVFVOCVCVDVEVGVHVOCVIVJSVPVQWCVKVLTVMVN $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d B a x z $.  $d ph y $.  $d ps x $.  $d ch x $.  $d ph a z $.
    $d a x y $.
    setindtrs.a $e |- ( A. y e. x ps -> ph ) $.
    setindtrs.b $e |- ( x = y -> ( ph <-> ps ) ) $.
    setindtrs.c $e |- ( x = B -> ( ph <-> ch ) ) $.
    $( Epsilon induction scheme without Infinity.  See comments at
       ~ setindtr. $)
    setindtrs $p |- ( E. z ( Tr z /\ B e. z ) -> ch ) $=
      ( va cv wtr wcel wa wex wi wral hbab1 cvv cab setindtr dfss3 ax17el hbral
      wss hbim weq raleq eleq1 imbi12d vex elab ralbii abid 3imtr4i chvar sylbi
      mpg wb elex adantl exlimiv elabg syl mpbid ) FLZMZGVGNZOZFPZGADUAZNZCKLZV
      LUFZVNVLNZQVKVMQKKFVLGUBVOELZVLNZEVNRZVPEVNVLUCVREDLZRZVTVLNZQVSVPQDKVSVP
      DVRDEVNEKDUDADESUEADKSUGDKUHWAVSWBVPVREVTVNUIVTVNVLUJUKBEVTRAWAWBHVRBEVTA
      BDVQEULIUMUNADUOUPUQURUSVKGTNZVMCUTVJWCFVIWCVHGVGVAVBVCACDGTJVDVEVF $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d a b c x y $.  $d N a b c x y $.

    $( Lemma for ~ dford3 . $)
    dford3lem1 $p |- ( ( Tr N /\ A. y e. N Tr y ) ->
        A. b e. N ( Tr b /\ A. y e. b Tr y ) ) $=
      ( wtr cv wral wa treq cbvralv biimpi adantl wcel wi wss trss ssralv com23
      syl6 imp ralrimiv r19.26 sylanbrc ) BDZAEZDZABFZGZCEZDZCBFZUEAUHFZCBFUIUK
      GCBFUFUJUCUFUJUEUIACBUDUHHIJKUGUKCBUCUFUHBLZUKMUCULUFUKUCULUHBNUFUKMBUHOU
      EAUHBPRQSTUIUKCBUAUB $.
      $( [28-Oct-2014] $)

    $( Lemma for ~ dford3 . $)
    dford3lem2 $p |- ( ( Tr x /\ A. y e. x Tr y ) -> x e. On ) $=
      ( vc va vb cv wtr wa wral con0 wcel vex treq anbi12d wi word sylibr raleq
      weq eleq1 wel wex csuc trsuc2 sucid sucex eleq2 cla4ev sylancl adantr wss
      wceq simprl dford3lem1 ralim syl5 imp dfss3 ordon trssord syl3anc elon ex
      a1i imbi12d setindtrs mpcom ) CFZGZACUAZHZCUBZAFZGZBFGZBVMIZHZVMJKZVNVLVP
      VNVMUCZGZVMVSKZVLVMUDVMALZUEVKVTWAHCVSVMWBUFVHVSULVIVTVJWAVHVSMVHVSVMUGNU
      HUIUJDFZGZVOBWCIZHZWCJKZOEFZGZVOBWHIZHZWHJKZOZVQVRODECVMWMEWCIZWFWGWNWFHZ
      WCPZWGWOWDWCJUKZJPZWPWNWDWEUMWOWLEWCIZWQWNWFWSWFWKEWCIWNWSBWCEUNWKWLEWCUO
      UPUQEWCJURQWRWOUSVDWCJUTVAWCDLVBQVCDESZWFWKWGWLWTWDWIWEWJWCWHMVOBWCWHRNWC
      WHJTVEDASZWFVQWGVRXAWDVNWEVPWCVMMVOBWCVMRNWCVMJTVEVFVG $.
      $( [28-Oct-2014] $)

    $( Ordinals are precisely the hereditarily transitive classes. $)
    dford3 $p |- ( Ord N <-> ( Tr N /\ A. x e. N Tr x ) ) $=
      ( va word wtr cv wral wa ordtr wcel ordelord syl ralrimiva jca con0 simpl
      wss dford3lem1 dford3lem2 ralimi dfss3 biimpri 3syl ordon trssord syl3anc
      a1i impbii ) BDZBEZAFZEZABGZHZUIUJUMBIUIULABUIUKBJHUKDULBUKKUKILMNUNUJBOQ
      ZODZUIUJUMPUNCFZEULAUQGHZCBGUQOJZCBGZUOABCRURUSCBCASTUOUTCBOUAUBUCUPUNUDU
      GBOUEUFUH $.
      $( [28-Oct-2014] $)

    $( ~ dford3 expressed in primitives to demonstrate shortness. $)
    dford4 $p |- ( Ord N <-> A. a A. b A. c ( ( a e. N /\ b e. a ) ->
        ( b e. N /\ ( c e. b -> c e. a ) ) ) ) $=
      ( wtr cv wa wel wi wal dftr2 ax-17 ancom imbi1i bitri 2albii alcom bitr4i
      wcel impexp word dford3 df-ral imbi2i 19.21-2 bicomi anbi2i anass 3bitr3i
      wral 19.3 3bitri albii anbi12i 19.26 19.26-2 pm4.76 bitr3i ) AUAAEZBFZEZB
      AUJZGZUTASZCBHZGZCFASZIZDJZCJZVFDCHZDBHZIZIZDJCJZGZBJZVFVGVMGIZDJCJZBJBAU
      BVCVJBJZVOBJZGVQUSVTVBWAUSVEVDGZVGIZBJCJZVTCBAKVTWCCJBJWDVIWCBCVIVHWCVHDV
      HDLUKVFWBVGVDVEMNOPWCBCQORVBVDVAIZBJWAVABAUCWEVOBWEVDVKVEGZVLIZCJDJZIZVDW
      GIZCJDJZVOVAWHVDDCUTKUDWKWIVDWGDCVDDLVDCLUEUFWKVNCJDJVOWJVNDCVDWFGZVLIVFV
      KGZVLIWJVNWLWMVLWLVDVEVKGZGWMWFWNVDVKVEMUGVDVEVKUHRNVDWFVLTVFVKVLTUIPVNDC
      QOULUMOUNVJVOBUORVPVSBVPVHVNGZDJCJVSVHVNCDUPWOVRCDVFVGVMUQPURUMUL $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d ph y $.  $d x y $.  $d A y a $.
    $( Two ways to express "exactly one". $)
    reuen1 $p |- ( E! x e. A ph <-> { x e. A | ph } ~~ 1o ) $=
      ( vy wreu crab cv csn wceq wex c1o cen wbr reusn en1 bitr4i ) ABCEABCFZDG
      HIDJQKLMABDCNDQOP $.
      $( [28-Oct-2014] $)

    $( Two ways to express "exactly one". $)
    euen1 $p |- ( E! x ph <-> { x | ph } ~~ 1o ) $=
      ( cvv wreu crab c1o cen wbr weu cab reuen1 reuv rabab breq1i 3bitr3i ) AB
      CDABCEZFGHABIABJZFGHABCKABLPQFGABMNO $.
      $( [28-Oct-2014] $)

    $( A set has less than one member iff it is empty. $)
    sdom1 $p |- ( A ~< 1o <-> A = (/) ) $=
      ( va c1o csdm wbr c0 wceq wcel relsdom brrelexi cv wi breq1 eqeq1 imbi12d
      cvv wn cdom domnsym 0sdom con2i 0sdom1dom biimpi necon2bbii sylibr vtoclg
      vex nsyl mpcom wne 1n0 con0 1on elexi mpbir mpbiri impbii ) ACDEZAFGZAPHU
      RUSACDIJBKZCDEZUTFGZLURUSLBAPUTAGVAURVBUSUTACDMUTAFNOVAFUTDEZQVBVACUTREZV
      CVDVACUTSUAVCVDUTBUGZUBUCUHVCUTFUTVETUDUEUFUIUSURFCDEZVFCFUJUKCCULUMUNTUO
      AFCDMUPUQ $.
      $( [28-Oct-2014] $)

    $( Two ways to express "at most one". $)
    modom $p |- ( E* x ph <-> { x | ph } ~<_ 1o ) $=
      ( wmo wex weu wi wn wo cab c1o cdom wbr df-mo imor csdm cen c0 wceq sdom1
      abn0 necon1bbii eqid1 mpbir breq1 mpbiri biimpi impbii bitri euen1 brdom2
      orbi12i bitr4i 3bitri ) ABCABDZABEZFUNGZUOHZABIZJKLZABMUNUONUQURJOLZURJPL
      ZHUSUPUTUOVAUPURQRZUTUNURQABTUAVBUTVBUTQJOLZVCQQRQUBQSUCURQJOUDUEUTVBURSU
      FUGUHABUIUKURJUJULUM $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d a b c d e f g h i j k l m $.  $d A a b c $.  $d B a b c $.
    $d C a b c $.

    $( Lemma for ~ ttac .  Use non-surjection to prove non-emptiness. $)
    ttaclem4 $p |- ( ( ( ( b i^i a ) = (/) /\ e e. ( b u. a ) ) /\
        -. b ~<_ a /\ d : ( ( b u. a ) X. ( b u. a ) ) -1-1-onto->
        ( b u. a ) ) -> ( b i^i ( d " ( b X. { e } ) ) ) =/= (/) ) $=
      ( vf vg vh cv cin c0 wceq wcel wa wn wi vex wel ad2antlr opelxp sylanbrc
      cun cdom wbr cxp wf1o w3a csn cima wne simp2 cvv cop wo wfun f1ofun elun1
      cfv cdm adantl simpllr f1odm eleqtrrd simpr snid a1i funfvima imp adantlr
      syl21anc incom eqeq1i wral disj eleq1 notbid rcla4v com12 mpd wf f1of syl
      sylbi simplr ad2antrr ffvelrn syl2anc elun sylib orel1 sylc ex weq wb wf1
      f1of1 ad2antrl ad2antll jca f1fveq biimpd opth simplbi syl6 opeq1 impbid1
      fveq2d adantr dom2d mpi necon3bd 3adant2 ) CHZBHZIJKZAHZXLXMUAZLZMZXLXMUB
      UCZNZXPXPUDZXPDHZUEZUFXTXLYBXLXOUGZUDZUHZIZJUIZXRXTYCUJXRYCXTYHOXTXRYCMZX
      SYGJYIYGJKZXSYIYJMZXLUKLXSCPYKEFXLXMEHZXOULZYBUQZFHZXOULZYBUQZUKYKECQZYNX
      MLZYKYRMZYNXLLZNZUUAYSUMZYSYTYNYFLZUUBYIYRUUDYJYIYRMZYBUNZYMYBURZLZYMYELZ
      UUDYCUUFXRYRYAXPYBUORUUEYMYAUUGUUEYLXPLZXQYMYALZYRUUJYIYLXLXMUPZUSXNXQYCY
      RUTYLXOXPXPAPZSZTYCUUGYAKXRYRYAXPYBVARVBUUEYRXOYDLZUUIYIYRVCUUOUUEXOUUMVD
      VEYLXOXLYDUUMSTUUFUUHMUUIUUDYEYMYBVFVGVIVHYJUUDUUBOZYIYRYJYFXLIZJKZUUPYGU
      UQJXLYFVJVKUURGCQZNZGYFVLZUUPGYFXLVMUUDUVAUUBUUTUUBGYNYFGHZYNKUUSUUAUVBYN
      XLVNVOVPVQWBWBRVRYTYNXPLZUUCYTYAXPYBVSZUUKUVCYTYCUVDXRYCYJYRUTYAXPYBVTWAY
      TUUJXQUUKYRUUJYKUULUSYIXQYJYRXNXQYCWCWDUUNTYAXPYMYBWEWFYNXLXMWGWHUUAYSWIW
      JWKYIYRFCQZMZYNYQKZEFWLZWMZOYJYIUVFUVIYIUVFMZUVGUVHUVJUVGYMYPKZUVHUVJUVGU
      VKUVJYAXPYBWNZUUKYPYALZMZUVGUVKWMYCUVLXRUVFYAXPYBWORXRUVFUVNYCXRUVFMZUUKU
      VMUVOUUJXQUUKYRUUJXRUVEUULWPXNXQUVFWCZUUNTUVOYOXPLZXQUVMUVEUVQXRYRYOXLXMU
      PWQUVPYOXOXPXPUUMSTWRVHYAXPYMYPYBWSWFWTUVKUVHAAWLYLXOYOXOEPUUMUUMXAXBXCUV
      HYMYPYBYLYOXOXDXFXEWKXGXHXIWKXJXKVR $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ ttac . $)
    ttaclem5 $p |- ( ( ( ( b i^i a ) = (/) /\ -. b ~<_ a /\ d : ( ( b u. a ) X.
        ( b u. a ) ) -1-1-onto-> ( b u. a ) ) /\ b e. On ) -> a ~<_ b ) $=
      ( ve vf vg cv cin c0 wceq cxp con0 wcel wa cima wss wne adantl simpll3 ex
      cdom wbr wn cun wf1o w3a cvv vex csn cint wel inss1 onss ad2antlr simpll1
      syl5ss elun2 simpll2 ttaclem4 syl211anc syl2anc sseldi weq wb wex adantrr
      onint adantr wi adantrl eleq1a syl imp elin sylanbrc eleq1 cla4egv inindi
      sylc n0 ccnv wfun wf1 f1of1 wf df-f1 simprbi eqcomd ineq2d xpindi imaeq2i
      imain ineq2i disjsn2 xpeq2d imaeq2d xp0 in0 3eqtri syl6eq syl5eqr necon1d
      ima0 eqtrd syl5bir sylsyld sneq inteqd impbid1 dom2d mpi ) BGZAGZHIJZXLXM
      UAUBUCZXLXMUDZXPKZXPCGZUEZUFZXLLMZNZXMUGMXMXLUAUBAUHYBDEXMXLXLXRXLDGZUIZK
      ZOZHZUJZXLXRXLEGZUIZKZOZHZUJZUGYBDAUKZYHXLMYBYONZYGXLYHXLYFULZYPYGLPYGIQZ
      YHYGMZYPYGXLLYQYAXLLPZXTYOXLUMZUNUPYPXNYCXPMZXOXSYRXNXOXSYAYOUOYOUUBYBYCX
      MXLUQRXNXOXSYAYOURXNXOXSYAYOSDABCUSUTYGVGVAZVBTYBYOEAUKZNZYHYNJZDEVCZVDYB
      UUENZUUFUUGUUHXSUUFFGZYGYMHZMZFVEZUUGXNXOXSYAUUESUUHUUFUULUUHUUFNZYSYHUUJ
      MZUULUUHYSUUFYBYOYSUUDUUCVFVHZUUMYSYHYMMZUUNUUOUUHUUFUUPUUHYNYMMZUUFUUPVI
      YBUUDUUQYOYBUUDNZYMLPYMIQZUUQUURYMXLLXLYLULYAYTXTUUDUUAUNUPUURXNYIXPMZXOX
      SUUSXNXOXSYAUUDUOUUDUUTYBYIXMXLUQRXNXOXSYAUUDURXNXOXSYAUUDSEABCUSUTYMVGVA
      VJYNYMYHVKVLVMYHYGYMVNVOUUKUUNFYHYGUUIYHUUJVPVQVSTUULUUJIQXSUUGFUUJVTXSYC
      YIUUJIXSYCYIQZUUJIJXSUVANZUUJXLYFYLHZHZIXLYFYLVRUVBUVDXLXRYEYKHZOZHZIUVBU
      VCUVFXLUVBUVFUVCUVBXRWAWBZUVFUVCJXSUVHUVAXSXQXPXRWCZUVHXQXPXRWDUVIXQXPXRW
      EUVHXQXPXRWFWGVLVHYEYKXRWLVLWHWIUVBUVGXLXRXLYDYJHZKZOZHZIUVLUVFXLUVKUVEXR
      XLYDYJWJWKWMUVAUVMIJXSUVAUVMXLXRXLIKZOZHZIUVAUVLUVOXLUVAUVKUVNXRUVAUVJIXL
      YCYIWNWOWPWIUVPXLXRIOZHXLIHIUVOUVQXLUVNIXRXLWQWKWMUVQIXLXRXCWMXLWRWSWTRXA
      XDXATXBXEXFUUGYGYMUUGYFYLXLUUGYEYKXRUUGYDYJXLYCYIXGWOWPWIXHXITXJXK $.
    $( [5-Nov-2014] $)

    $( Lemma for ~ ttac . $)
    ttaclem6 $p |- ( ( ( ( b i^i a ) = (/) /\ -. b ~<_ a /\ -. a e. Fin ) /\
        ( b e. On /\ A. c ( om ~<_ c -> ( c X. c ) ~~ c ) ) ) -> a ~<_ b ) $=
      ( vd cv wceq cdom wbr wn wcel com cxp cen wi wa wss wex syl vex cvv isinf
      cin cfn w3a con0 wal cun simpl2 wral weq breq2 anbi2d exbidv rcla4v com12
      c0 3ad2ant3 ensym adantl ssdomg ax-mp adantr endomtr syl2anc exlimiv syld
      mtod word wb ordom eloni ordtri1 sylancr mpbird ssun1 syl6ss unex ssdom2g
      a1i xpeq12 anidms id breq12d imbi12d cla4v wf1o bren simpll1 simpr simplr
      simpll2 ttaclem5 syl31anc ex exlimdv syl5bi impr ) BEZAEZUBUPFZWRWSGHZIZW
      SUCJIZUDZWRUEJZKCEZGHZXFXFLZXFMHZNZCUFZWSWRGHZXDXEOZXKWRWSUGZXNLZXNMHZXLX
      MKXNGHZXKXPNXMKXNPZXQXMKWRXNXMKWRPZWRKJZIZXMXTXAWTXBXCXEUHXDXTXANXEXDXTDE
      ZWSPZYBWRMHZOZDQZXAXCWTXTYFNZXBXCYCYBXFMHZOZDQZCKUIZYGDWSCUAXTYKYFYJYFCWR
      KCBUJZYIYEDYLYHYDYCXFWRYBMUKULUMUNUORUQYFXANXDYEXADYEWRYBMHZYBWSGHZXAYDYM
      YCYBWRBSZURUSYCYNYDYBTJYCYNNDSYBWSTUTVAVBWRYBWSVCVDVEVSVFVBVGXMKVHWRVHZXS
      YAVIVJXEYPXDWRVKUSKWRVLVMVNWRWSVOVPXNTJXRXQNWRWSYOASVQZKXNTVRVARXKXQXPXJX
      QXPNCXNYQXFXNFZXGXQXIXPXFXNKGUKYRXHXOXFXNMYRXHXOFXFXNXFXNVTWAYRWBWCWDWEUO
      RXPXOXNXFWFZCQXMXLXOXNCYQWGXMYSXLCXMYSXLXMYSOWTXBYSXEXLWTXBXCXEYSWHWTXBXC
      XEYSWKXMYSWIXDXEYSWJABCWLWMWNWOWPVFWQ $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ ttac . $)
    ttaclem7 $p |- ( ( ( On i^i a ) = (/) /\ A. c ( om ~<_ c ->
        ( c X. c ) ~~ c ) ) -> E. b e. On b ~~ a ) $=
      ( vd cv wcel con0 cin c0 wceq cdom wbr cen wi wa wrex cvv breq1 syl2anc
      wn cfn com cxp wal finnum a1d hartogs ax-mp onirri cbvrabv elrab2 biimpri
      crab vex mpan mto notbid rcla4ev mp2an simprl wss ad2antrl simplrl ssdisj
      onss simprr simplrr ttaclem6 syl32anc ra4e ondomen syl expr rexlimdva mpi
      simpll ex pm2.61i ) AEZUAFZGVSHIJZUBCEZKLWBWBUCWBMLNCUDZOZBEZVSMLBGPZNVTW
      FWDBVSUEUFVTTZWDWFWGWDOZDEZVSKLZTZDGPZWFWEVSKLZBGUMZGFZWNVSKLZTZWLVSQFWOA
      UNBVSQUGUHZWPWNWNFZWNWRUIWOWPWSWRWSWOWPOWBVSKLZWPCWNGWNWBWNVSKRWMWTBCGWEW
      BVSKRUJUKULUOUPWKWQDWNGWIWNJWJWPWIWNVSKRUQURUSWHWKWFDGWHWIGFZWKWFWHXAWKOZ
      OZVSWIKLZDGPZWFXCXAXDXEWHXAWKUTZXCWIVSHIJZWKWGXAWCXDXCWIGVAZWAXGXAXHWHWKW
      IVEVBWGWAWCXBVCWIGVSVDSWHXAWKVFWGWDXBVPXFWGWAWCXBVGADCVHVIXDDGVJSDBVSVKVL
      VMVNVOVQVR $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ ttac . $)
    ttaclem8 $p |- ( A. c ( om ~<_ c -> ( c X. c ) ~~ c ) ->
        E. b e. On b ~~ a ) $=
      ( vd com cv wbr cxp cen wi c1o con0 wrex cin c0 wceq incom cvv eqtri wa
      cdom wal wss xpss onxpdisj ssdisj mp2an vex 1onn elexi xpex eqeq1d anbi1d
      ineq2 breq2 rexbidv imbi12d ttaclem7 vtocl mpan xp1en entr mpan2 reximi
      syl ) ECFZUAGVFVFHVFIGJCUBZBFZAFZKHZIGZBLMZVHVIIGZBLMLVJNZOPZVGVLVNVJLNZO
      LVJQVJRRHZUCVQLNZOPVPOPVIKUDVRLVQNOVQLQUESVJVQLUFUGSLDFZNZOPZVGTZVHVSIGZB
      LMZJVOVGTZVLJDVJVIKAUHZKEUIUJUKVSVJPZWBWEWDVLWGWAVOVGWGVTVNOVSVJLUNULUMWG
      WCVKBLVSVJVHIUOUPUQDBCURUSUTVKVMBLVKVJVIIGVMVIWFVAVHVJVIVBVCVDVE $.
      $( [5-Nov-2014] $)

    $( Tarski's theorem about choice: ~ infxpidm is equivalent to ~ ax-ac . $)
    ttac $p |- ( A. a E. b b We a <-> A. c ( om ~<_ c -> ( c X. c ) ~~ c ) ) $=
      ( vd cv wwe wex wal cen wbr con0 wrex com cdom cvv wcel vex con2i alrimiv
      wn cxp wi ween ax-mp albii weq breq2 rexbidv cla4v csdm isfinite3 domnsym
      wb cfn sylbi infxpidm2 ex syl5 syl ttaclem8 impbii bitri ) AEZBEFBGZAHDEZ
      VCIJZDKLZAHZMCEZNJZVIVIUAVIIJZUBZCHZVDVGAVCOPVDVGUMAQDVCOBUCUDUEVHVMVHVLC
      VHVEVIIJZDKLZVLVGVOAVICQZACUFVFVNDKVCVIVEIUGUHUIVJVIUNPZTZVOVKVQVJVQVIMUJ
      JZVJTVIUKVJVSMVIULRUORVOVRVKDVIVPUPUQURUSSVMVGAADCUTSVAVB $.
      $( [4-Nov-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Eight inequivalent definitions of finite set
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c {C.} $.

  $( Extend class notation to include the reified proper subset relation. $)
  crpss $a class {C.} $.

  ${
    $d a b $.
    $( Define a relation which corresponds to proper subsethood ~ df-pss on
       sets.  This allows us to use proper subsethood with general concepts
       that require relations, such as strict ordering, see ~ sorpss . $)
    df-rpss $a |- {C.} = { <. a , b >. | a C. b } $.

    $d A a b c x y $.  $d B a b $.  $d C a b $.

    $( The proper subset relation is a relation. $)
    relrpss $p |- Rel {C.} $=
      ( va vb cv wpss crpss df-rpss relopabi ) ACBCDABEABFG $.
      $( [2-Nov-2014] $)

    ${
      $( The proper subset relation on sets is the same as class proper
         subsethood. $)
      brrpssg $p |- ( B e. _V -> ( A {C.} B <-> A C. B ) ) $=
        ( va vb cvv wcel crpss wbr wpss relrpss brrelexi adantl simpl jca pssss
        wa wss id ssexg cv syl2anr psseq1 psseq2 df-rpss brabg pm5.21nd ) BEFZA
        BGHZABIZAEFZUGPUGUHPUJUGUHUJUGABGJKLUGUHMNUGUIPUJUGUIABQUGUJUGABOUGRABE
        SUAUGUIMNCTZDTZIAULIUICDABEEGUKAULUBULBAUCCDUDUEUF $.
        $( [2-Nov-2014] $)

      brrpss.a $e |- B e. _V $.
      $( The proper subset relation on sets is the same as class proper
         subsethood. $)
      brrpss $p |- ( A {C.} B <-> A C. B ) $=
        ( cvv wcel crpss wbr wpss wb brrpssg ax-mp ) BDEABFGABHICABJK $.
        $( [2-Nov-2014] $)
    $}

    $( Every class is partially ordered by proper subsets. $)
    porpss $p |- {C.} Po A $=
      ( va vb vc crpss wpo cv wbr wn wa wi wral wpss vex brrpss anbi12i imbi12i
      notbii pssirr psstr mpbir2an rgenw rgen2w df-po mpbir ) AEFBGZUFEHZIZUFCG
      ZEHZUIDGZEHZJZUFUKEHZKZJZDALZCALBALUQBCAAUPDAUPUFUFMZIZUFUIMZUIUKMZJZUFUK
      MZKZUHUSUOVDUGURUFUFBNORUMVBUNVCUJUTULVAUFUICNOUIUKDNZOPUFUKVEOQPUFSUFUIU
      KTUAUBUCBCDAEUDUE $.
      $( [2-Nov-2014] $)

    $( Express strict ordering under proper subsets, i.e. the notion of a chain
       of sets. $)
    sorpss $p |- ( {C.} Or A <-> A. x e. A A. y e. A ( x C_ y \/
        y C_ x ) ) $=
      ( cv crpss wbr weq w3o wral wpo wss wor porpss biantrur wpss sspsstri vex
      wa wo brrpss biid 3orbi123i bitr4i 2ralbii df-so 3bitr4ri ) ADZBDZEFZABGZ
      UHUGEFZHZBCIACIZCEJZUMRUGUHKUHUGKSZBCIACICELUNUMCMNUOULABCCUOUGUHOZUJUHUG
      OZHULUGUHPUIUPUJUJUKUQUGUHBQTUJUAUHUGAQTUBUCUDABCEUEUF $.
      $( [2-Nov-2014] $)

    $( Property of a chain of sets. $)
    sorpssi $p |- ( ( {C.} Or A /\ ( B e. A /\ C e. A ) ) ->
        ( B C_ C \/ C C_ B ) ) $=
      ( crpss wor wcel wa wpss wceq w3o wss wbr solin cvv elex ad2antll brrpssg
      wo wb syl biidd ad2antrl 3orbi123d mpbid sspsstri sylibr ) ADEZBAFZCAFZGG
      ZBCHZBCIZCBHZJZBCKCBKRUJBCDLZULCBDLZJUNABCDMUJUOUKULULUPUMUJCNFZUOUKSUIUQ
      UGUHCAOPBCQTUJULUAUJBNFZUPUMSUHURUGUIBAOUBCBQTUCUDBCUEUF $.
      $( [2-Nov-2014] $)

    $d F a b c d e f $.  $d R a b c d e f $.
    $( The range of a single-step monotone function from ` om ` into a
       partially ordered set is a chain. $)
    sornom $p |- ( ( F Fn om /\ A. a e. om ( ( F ` a ) R ( F ` suc a ) \/
          ( F ` a ) = ( F ` suc a ) ) /\ R Po ran F ) -> R Or ran F ) $=
      ( vb vc vd ve com cv cfv wbr wceq wo weq wcel wa wrex wi fveq2 orbi12d wb
      wfn csuc wral crn wpo w3a w3o wor simp3 fvelrnb anbi12d 3ad2ant1 wss word
      reeanv nnord ordtri2or2 syl2an adantl vex eleq1 bi2anan9 anbi2d breqan12d
      sseq12 eqeqan12d imbi12d breq2d eqeq2d imbi2d a1i12 simplll simpr2 fveq2d
      eqid suceq breq12d eqeq12d rcla4va syl2anc simprr simprl simpllr fnfvelrn
      olci peano2 ad3antrrr potr syl13anc ancom2s orcd expr breq1 biimprcd syl6
      imp orc jaod ex breq2 eqeq2 biimpd a1i 3adantr2 mpd findsg ancom1s impcom
      a2d vtocl2 orim12d 3mix1 3mix2 jaoi 3mix3 eqcoms syl breq12 eqeq12 ancoms
      3orbi123d syl5ibcom rexlimdvva syl5bir sylbid ralrimivv df-so sylanbrc )
      BHUBZCIZBJZYKUCZBJZAKZYLYNLZMZCHUDZBUEZAUFZUGZYTDIZEIZAKZDENZUUCUUBAKZUHZ
      EYSUDDYSUDYSAUIYJYRYTUJUUAUUGDEYSYSUUAUUBYSOZUUCYSOZPZFIZBJZUUBLZFHQZGIZB
      JZUUCLZGHQZPZUUGYJYRUUJUUSUAYTYJUUHUUNUUIUURFHUUBBUKGHUUCBUKULUMUUSUUMUUQ
      PZGHQFHQUUAUUGUUMUUQFGHHUPUUAUUTUUGFGHHUUAUUKHOZUUOHOZPZPZUULUUPAKZUULUUP
      LZUUPUULAKZUHZUUTUUGUVDUVEUVFMZUVGUUPUULLZMZMZUVHUVDUUKUUOUNZUUOUUKUNZMZU
      VLUVCUVOUUAUVAUUKUOUUOUOUVOUVBUUKUQUUOUQUUKUUOURUSUTUVDUVMUVIUVNUVKUUAUUB
      HOZUUCHOZPZPZUUBUUCUNZUUBBJZUUCBJZAKZUWAUWBLZMZRZRZUVDUVMUVIRZRDEUUKUUOFV
      AZGVAZDFNZEGNZPZUVSUVDUWFUWHUWMUVRUVCUUAUWKUVPUVAUWLUVQUVBUUBUUKHVBUUCUUO
      HVBVCVDUWMUVTUVMUWEUVIUUBUUKUUCUUOVFUWMUWCUVEUWDUVFUWKUWLUWAUULUWBUUPAUUB
      UUKBSZUUCUUOBSZVEUWKUWLUWAUULUWBUUPUWNUWOVGTVHVHUUAUVRUVTUWEUVRUVTPUUAUWE
      UVQUVPUVTUUAUWERZUUAUWAUULAKZUWAUULLZMZRUUAUWAUWAAKZUWAUWALZMZRUUAUWAUUPA
      KZUWAUUPLZMZRUUAUWAUUOUCZBJZAKZUWAUXGLZMZRUWPFGUUCUUBFDNZUWSUXBUUAUXKUWQU
      WTUWRUXAUXKUULUWAUWAAUUKUUBBSZVIUXKUULUWAUWAUXLVJTVKFGNZUWSUXEUUAUXMUWQUX
      CUWRUXDUXMUULUUPUWAAUUKUUOBSZVIUXMUULUUPUWAUXNVJTVKUUKUXFLZUWSUXJUUAUXOUW
      QUXHUWRUXIUXOUULUXGUWAAUUKUXFBSZVIUXOUULUXGUWAUXPVJTVKFENZUWSUWEUUAUXQUWQ
      UWCUWRUWDUXQUULUWBUWAAUUKUUCBSZVIUXQUULUWBUWAUXRVJTVKUVPUUAUXBUXAUWTUWAVP
      WFVLUVBUVPPUUBUUOUNZPZUUAUXEUXJUXTUUAUXEUXJRZUXTUUAPZUUPUXGAKZUUPUXGLZMZU
      YAUYBUVBYRUYEUVBUVPUXSUUAVMUXTYJYRYTVNYQUYECUUOHCGNZYOUYCYPUYDUYFYLUUPYNU
      XGAYKUUOBSZUYFYMUXFBYKUUOVQVOZVRUYFYLUUPYNUXGUYGUYHVSTVTWAUXTYJYTUYEUYARY
      RUXTYJYTPZPZUYCUYAUYDUYJUYCUYAUYJUYCPUXCUXJUXDUYJUYCUXCUXJUYJUYCUXCPPUXHU
      XIUYJUXCUYCUXHUYJUXCUYCPZUXHUYJYTUWAYSOZUUPYSOZUXGYSOZUYKUXHRUXTYJYTWBUYJ
      YJUVPUYLUXTYJYTWCZUVBUVPUXSUYIWDHUUBBWEWAUYJYJUVBUYMUYOUVBUVPUXSUYIVMHUUO
      BWEWAUYJYJUXFHOZUYNUYOUVBUYPUVPUXSUYIUUOWGWHHUXFBWEWAYSUWAUUPUXGAWIWJWQWK
      WLWMUYCUXDUXJRUYJUYCUXDUXHUXJUXDUXHUYCUWAUUPUXGAWNWOUXHUXIWRWPUTWSWTUYDUY
      ARUYJUYDUXEUXJUYDUXCUXHUXDUXIUUPUXGUWAAXAUUPUXGUWAXBTXCXDWSXEXFWTXJXGXHXI
      WMZXKUUAUVBUVAUVNUVKRZUWGUUAUVBUVAPZPZUYRRDEUUOUUKUWJUWIDGNZEFNZPZUVSUYTU
      WFUYRVUCUVRUYSUUAVUAUVPUVBVUBUVQUVAUUBUUOHVBUUCUUKHVBVCVDVUCUVTUVNUWEUVKU
      UBUUOUUCUUKVFVUCUWCUVGUWDUVJVUAVUBUWAUUPUWBUULAUUBUUOBSZUUCUUKBSZVEVUAVUB
      UWAUUPUWBUULVUDVUEVGTVHVHUYQXKWKXLXFUVIUVHUVKUVEUVHUVFUVEUVFUVGXMUVFUVEUV
      GXNZXOUVGUVHUVJUVGUVEUVFXPUVHUULUUPVUFXQXOXOXRUUTUVEUUDUVFUUEUVGUUFUULUUB
      UUPUUCAXSUULUUBUUPUUCXTUUQUUMUVGUUFUAUUPUUCUULUUBAXSYAYBYCYDYEYFYGDEYSAYH
      YI $.
      $( [3-Nov-2014] $)
  $}


  $c Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 $.

  $( Extend class notation to include the class of Ia-finite sets. $)
  cfin1a $a class Fin1a $.

  $( Extend class notation to include the class of II-finite sets. $)
  cfin2 $a class Fin2 $.

  $( Extend class notation to include the class of III-finite sets. $)
  cfin3 $a class Fin3 $.

  $( Extend class notation to include the class of IV-finite sets. $)
  cfin4 $a class Fin4 $.

  $( Extend class notation to include the class of V-finite sets. $)
  cfin5 $a class Fin5 $.

  $( Extend class notation to include the class of VI-finite sets. $)
  cfin6 $a class Fin6 $.

  $( Extend class notation to include the class of VII-finite sets. $)
  cfin7 $a class Fin7 $.

  ${
    $d x y z w a b c d $.
    $( A set is Ia-finite iff it is not the union of two I-infinite sets.  This
       is the second of eight definitions of finite set attributed to Tarski;
       see http://consequences.emich.edu/note-94.pdf .  I-finite is equivalent
       to our ~ df-fin and not repeated here.  These eight definitions are
       equivalent with Choice but strictly decreasing in strength in models
       where Choice fails; conversely, they provide a series of increasingly
       stronger notions of infiniteness. $)
    df-fin1a $a |- Fin1a = { x | -. E. y E. z ( ( x = ( y u. z ) /\
      ( y i^i z ) = (/) ) /\ ( -. y e. Fin /\ -. z e. Fin ) ) } $.

    $( A set is II-finite (Tarski finite) iff every nonempty chain of subsets
       contains a maximum element. $)
    df-fin2 $a |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      {C.} Or y ) -> E. z e. y A. w e. y -. z C. w ) } $.

    $( A set is IV-finite (Dedekind finite) iff it has no equinumerous proper
       subset. $)
    df-fin4 $a |- Fin4 = { x | -. E. y ( y C. x /\ y ~~ x ) } $.

    $( A set is III-finite (weakly Dedekind finite) iff its power set is
       Dedekind finite. $)
    df-fin3 $a |- Fin3 = { x | ~P x e. Fin4 } $.

    $( A set is V-finite iff it behaves finitely under ` +c ` . $)
    df-fin5 $a |- Fin5 = { x | ( x ~~ (/) \/ x ~< ( x +c x ) ) } $.

    $( A set is VI-finite iff it behaves finitely under ` X. ` . $)
    df-fin6 $a |- Fin6 = { x | ( x ~~ (/) \/ x ~~ 1o \/ x ~< ( x X. x ) ) } $.

    $( A set is VII-finite iff it cannot be infinitely well ordered. $)
    df-fin7 $a |- Fin7 = { x | -. E. y e. ( On \ om ) x ~~ y } $.
  $}

  ${
    $d A a $.  $d B a $.

    $( A finite set is strictly dominated by another iff their cardinalities
       are strictly ordered.  TODO: ~ ficarddom has a statement which is not
       consistent with related theorems. $)
    ficardsdom $p |- ( ( A e. Fin /\ B e. Fin ) -> ( ( card ` A ) e.
      ( card ` B ) <-> A ~< B ) ) $=
      ( cfn wcel wa ccrd cfv wss wne cdom wbr wn csdm ficarddom bicomd ficarden
      cen necon3abid con0 cardon anbi12d wb onelpss mp2an brsdom 3bitr4g ) ACDB
      CDEZAFGZBFGZHZUHUIIZEZABJKZABQKZLZEUHUIDZABMKUGUJUMUKUOUGUMUJABNOUGUNUHUI
      ABPRUAUHSDUISDUPULUBATBTUHUIUCUDABUEUF $.
      $( [30-Oct-2014] $)

    $( Trichotomy of dominance without AC when one set is finite. $)
    fidomtri $p |- ( A e. Fin -> ( A ~<_ B <-> -. B ~< A ) ) $=
      ( va cfn wcel cdom wbr csdm wn domnsym wi ccrd cfv wss con0 cardon ancoms
      wa wb cvv ficarddom ontri1 mp2an ficardsdom notbid syl5bb biimprd wf1 wex
      bitrd cv isinffi vex f1f dmfex sylancr f1domg mpcom exlimiv syl pm2.61dan
      wf a1d impbid2 ) ADEZABFGZBAHGZIZABJVEBDEZVHVFKVEVIRZVFVHVJVFALMZBLMZNZVH
      ABUAVMVLVKEZIZVJVHVKOEVLOEVMVOSAPBPVKVLUBUCVJVNVGVIVEVNVGSBAUDQUEUFUJUGVE
      VIIZRVFVHVPVEVFVPVERABCUKZUHZCUIVFBACULVRVFCATEZVRVFVRVQTEABVQVBVSCUMABVQ
      UNABTVQUOUPABTVQUQURUSUTQVCVAVD $.
      $( [30-Oct-2014] $)
  $}

  ${
    fidomtri2.a $e |- A e. _V $.
    $( Trichotomy of dominance without AC when one set is finite. $)
    fidomtri2 $p |- ( B e. Fin -> ( A ~<_ B <-> -. B ~< A ) ) $=
      ( cfn wcel cdom wbr csdm wn domnsym cen wa sdomdom con3i fidomtri syl5ibr
      wi ensym endom syl a1i jcad brsdom syl6ibr con1d impbid2 ) BDEZABFGZBAHGZ
      IABJUGUHUIUGUHIZBAFGZBAKGZIZLUIUGUJUKUMUJUKUGABHGZIUNUHABMNBAOPUJUMQUGULU
      HULABKGUHBACRABSTNUAUBBAUCUDUEUF $.
      $( [30-Oct-2014] $)

    $( A set with less than two elements has 0 or 1. $)
    sdom2en01 $p |- ( A ~< 2o <-> ( A ~~ (/) \/ A ~~ 1o ) ) $=
      ( c2o wbr cfn wcel c0 cen c1o wo com con0 0fin ccrd cfv wceq eqeq2i mpan2
      wb syl5bbr csdm cdom cin onfin2 inss2 eqsstri 2onn sselii sdomdom sylancr
      domfi enfi mpan mpbiri 1onn jaoi csn fvex elpr df2o2 eleq2i df1o2 3bitr4i
      cpr orbi2i a1i cardnn ax-mp ficardsdom ficarden orbi12d 3bitr3d pm5.21nii
      card0 ) ACUADZAEFZAGHDZAIHDZJZVOCEFZACUBDVPKECKLEUCEUDLEUEUFZUGUHZACUICAU
      KUJVQVPVRVQVPGEFZMWCVQVPWCSMAGEULUMUNVRVPIEFZKEIWAUOUHZWDVRVPWDSWEAIEULUM
      UNUPVPANOZCFZWFGPZWFIPZJZVOVSWGWJSVPWFGGUQZVDZFWHWFWKPZJWGWJWFGWKANURUSCW
      LWFUTVAWIWMWHIWKWFVBQVEVCVFWGWFCNOZFZVPVOWNCWFCKFWNCPUGCVGVHVAVPVTWOVOSWB
      ACVIRTVPWHVQWIVRWHWFGNOZPZVPVQWPGWFVNQVPWCWQVQSMAGVJRTWIWFINOZPZVPVRWRIWF
      IKFWRIPUOIVGVHQVPWDWSVRSWEAIVJRTVKVLVM $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d a b c d f x y $.  $d ph b c d $.  $d G b c d $.
    infpssrlem.a $e |- ( ph -> x C_ a ) $.
    infpssrlem.c $e |- ( ph -> f : x -1-1-onto-> a ) $.
    infpssrlem.d $e |- ( ph -> y e. ( a \ x ) ) $.
    infpssrlem.e $e |- G = ( rec ( `' f , y ) |` om ) $.
    $( Lemma for ~ infpssr . $)
    infpssrlem1 $p |- ( G ` (/) ) = y $=
      ( c0 cfv cv ccnv crdg com cres fveq1i cvv wcel wceq vex fr0g ax-mp eqtri
      ) KELKDMNZCMZOPQZLZUGKEUHJRUGSTUIUGUACUBUGSUFUCUDUE $.
      $( [30-Oct-2014] $)

    $( Lemma for ~ infpssr . $)
    infpssrlem2 $p |- ( B e. om -> ( G ` suc B ) = ( `' f ` ( G ` B ) ) ) $=
      ( com wcel csuc cv ccnv crdg cres cfv fveq1i frsuc fveq2i 3eqtr4g ) DLMDN
      ZEOPZCOZQLRZSDUGSZUESUDFSDFSZUESUFDUEUAUDFUGKTUIUHUEDFUGKTUBUC $.
      $( [30-Oct-2014] $)

    $( Lemma for ~ infpssr . $)
    infpssrlem3 $p |- ( ph -> G : om --> a ) $=
      ( vc vb com wfn cv cfv wcel c0 fveq2 eleq1d wral wf ccnv crdg cres frfnom
      fneq1i mpbir a1i csuc wceq weq infpssrlem1 wel eldifi syl syl5eqel wa wss
      cdif adantr wf1o f1ocnv f1of 3syl ffvelrn sylan infpssrlem2 syl5ibr exp3a
      sseldd finds2 com12 ralrimiv ffnfv sylanbrc ) AEMNZKOZEPZFOZQZKMUAMVTEUBV
      QAVQDOZUCZCOZUDMUEZMNWDWCUFMEWEJUGUHUIAWAKMVRMQAWAWAREPZVTQLOZEPZVTQZWGUJ
      ZEPZVTQZAKLVRRUKVSWFVTVRRESTKLULVSWHVTVRWGESTVRWJUKVSWKVTVRWJESTAWFWDVTAB
      CDEFGHIJUMAWDVTBOZUTQCFUNIWDVTWMUOUPUQWGMQZAWIWLAWIURZWLWNWHWCPZVTQWOWMVT
      WPAWMVTUSWIGVAAVTWMWCUBZWIWPWMQAWMVTWBVBVTWMWCVBWQHWMVTWBVCVTWMWCVDVEVTWM
      WHWCVFVGVKWNWKWPVTABCWGDEFGHIJVHTVIVJVLVMVNKMVTEVOVP $.
      $( [30-Oct-2014] $)

    $d B b c $.  $d C b c $.
    $( Lemma for ~ infpssr . $)
    infpssrlem4 $p |- ( ( ph /\ B e. om /\ C e. B ) -> ( G ` B ) =/= ( G ` C )
        ) $=
      ( vb com wcel cfv wne wa wi wceq vc vd cv wral c0 fveq2 neeq1d raleqbi1dv
      csuc imbi2d weq ral0 a1i w3a ccnv infpssrlem2 adantr wel wf1o f1ocnv f1of
      wn 3syl adantl infpssrlem3 ffvelrn sylan ancoms syl2anc eldifn syl nelne2
      cdif eqnetrd 3adant3 infpssrlem1 syl6eq neeq2d syl5ibr adantrd wrex simpr
      wf peano2 elnn 3ad2antl1 simpl nnsuc ax-17 hbra1 hb3an hban word wb nnord
      simpl3 ordsucelsuc mpbird adantrr ra4 wf1 f1of1 ad2antlr adantll syl12anc
      sylc necon3bid biimprd neeq12d adantlr sylibrd adantrl 3adantl3 mpd eleq1
      f1fveq anbi2d imbi12d mpbiri com3l rexlimd ex pm2.61ine ralrimiva cbvralv
      expr sylib 3exp a2d finds impcom rcla4cv 3impia ) ADNOZEDOZDGPZEGPZQZAYNR
      YPMUCZGPZQZMDUDZYOYRSYNAUUBAUAUCZGPZYTQZMUUCUDZSAUEGPZYTQZMUEUDZSAUBUCZGP
      ZYTQZMUUJUDZSAUUJUIZGPZYTQZMUUNUDZSAUUBSUAUBDUUCUETZUUFUUIAUUEUUHMUUCUEUU
      RUUDUUGYTUUCUEGUFZUGUHUJUAUBUKZUUFUUMAUUEUULMUUCUUJUUTUUDUUKYTUUCUUJGUFUG
      UHUJUUCUUNTZUUFUUQAUUEUUPMUUCUUNUVAUUDUUOYTUUCUUNGUFUGUHUJUUCDTZUUFUUBAUU
      EUUAMUUCDUVBUUDYPYTUUCDGUFUGUHUJUUIAUUHMULUMUUJNOZAUUMUUQUVCAUUMUUQUVCAUU
      MUNZUUOUUDQZUAUUNUDUUQUVDUVEUAUUNUVDUUCUUNOZRZUVESUUCUEUURUVDUVEUVFUVDUVE
      UURUUOCUCZQZUVCAUVIUUMUVCARZUUOUUKFUCZUOZPZUVHUVCUUOUVMTZAABCUUJFGHIJKLUP
      ZUQUVJUVMBUCZOZCBURVBZUVMUVHQUVJHUCZUVPUVLWCZUUKUVSOZUVQAUVTUVCAUVPUVSUVK
      USZUVSUVPUVLUSZUVTJUVPUVSUVKUTZUVSUVPUVLVAVCVDAUVCUWAANUVSGWCZUVCUWAABCFG
      HIJKLVEZNUVSUUJGVFVGVHZUVSUVPUUKUVLVFVIAUVRUVCAUVHUVSUVPVMOUVRKUVHUVSUVPV
      JVKVDUVMUVHUVPVLVIVNVOUURUUDUVHUUOUURUUDUUGUVHUUSABCFGHIJKLVPVQVRVSVTUUCU
      EQZUVGUVEUWHUVGRZUUCYSUIZTZMNWAZUVEUWIUUCNOZUWHUWLUVGUWMUWHUVCAUVFUWMUUMU
      VCUVFRUVFUUNNOZUWMUVCUVFWBUVCUWNUVFUUJWDUQUUCUUNWEVIWFVDUWHUVGWGMUUCWHVIU
      VGUWLUVESUWHUVGUWKUVEMNUVDUVFMUVCAUUMMUVCMWIAMWIUULMUUJWJWKUVFMWIWLUVEMWI
      UWKUVGYSNOZUVEUWKUVGUWOUVESZSUVDUWJUUNOZRZUWOUUOUWJGPZQZSZSUVDUWQUWOUWTUV
      DUWQUWORZRZUULUWTUXCUUMMUBURZUULUVCAUUMUXBWPUVDUWQUXDUWOUVCAUWQUXDUUMUVCU
      WQRZUXDUWQUVCUWQWBUXEUUJWMZUXDUWQWNUVCUXFUWQUUJWOUQYSUUJWQVKWRWFWSUULMUUJ
      WTXFUVCAUXBUULUWTSZUUMUVJUWOUXGUWQUVJUWORZUULUVMYTUVLPZQZUWTUXHUXJUULUXHU
      VMUXIUUKYTUXHUVSUVPUVLXAZUWAYTUVSOZUVMUXITUUKYTTWNAUXKUVCUWOAUWBUWCUXKJUW
      DUVSUVPUVLXBVCXCUVJUWAUWOUWGUQAUWOUXLUVCAUWEUWOUXLUWFNUVSYSGVFVGXDUVSUVPU
      UKYTUVLXPXEXGXHUVCUWOUWTUXJWNAUVCUWORUUOUVMUWSUXIUVCUVNUWOUVOUQUWOUWSUXIT
      UVCABCYSFGHIJKLUPVDXIXJXKXLXMXNYFUWKUVGUWRUWPUXAUWKUVFUWQUVDUUCUWJUUNXOXQ
      UWKUVEUWTUWOUWKUUDUWSUUOUUCUWJGUFVRUJXRXSXTYAVDXNYBYCYDUVEUUPUAMUUNUAMUKU
      UDYTUUOUUCYSGUFVRYEYGYHYIYJYKUUAYRMEDYSETYTYQYPYSEGUFVRYLVKYM $.
      $( [30-Oct-2014] $)

    $( Lemma for ~ infpssr . $)
    infpssrlem5 $p |- ( ph -> om ~<_ a ) $=
      ( vb vc com cv cfv wi wral wcel wa wel wf1 cdom wbr wf weq infpssrlem3 wo
      wceq wn simpll simplrr simpr infpssrlem4 syl3anc necomd simplrl jaodan ex
      wne necon2bd wb word nnord ordtri3 syl2an adantl sylibrd ralrimivva dff13
      sylanbrc cvv vex f1dom2g ax-mp syl ) AMFNZEUAZMVPUBUCZAMVPEUDKNZEOZLNZEOZ
      UHZKLUEZPZLMQKMQVQABCDEFGHIJUFAWEKLMMAVSMRZWAMRZSZSZWCKLTZLKTZUGZUIZWDWIW
      LVTWBWIWLVTWBUSZWIWJWNWKWIWJSZWBVTWOAWGWJWBVTUSAWHWJUJAWFWGWJUKWIWJULABCW
      AVSDEFGHIJUMUNUOWIWKSAWFWKWNAWHWKUJAWFWGWKUPWIWKULABCVSWADEFGHIJUMUNUQURU
      TWHWDWMVAZAWFVSVBWAVBWPWGVSVCWAVCVSWAVDVEVFVGVHKLMVPEVIVJVPVKRVQVRPFVLMVP
      VKEVMVNVO $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d a x c y f A $.  $d a x c y f X $.
    infpssr.a $e |- A e. _V $.
    $( Dedekind infinity implies existance of a denumerable subset: take a
       single point witnessing the proper subset relation and iterate the
       embedding.  The hypothesis is technically redundant with our current
       ~ df-op . $)
    infpssr $p |- ( ( X C. A /\ X ~~ A ) -> om ~<_ A ) $=
      ( va vx vy vf cv wpss cen wbr wa com cdom wi wceq breq2 anbi12d cvv wcel
      psseq2 imbi12d relen brrelexi psseq1 imbi1d wel wn wex pssnel adantr cdif
      breq1 eldif wss pssss wf1o bren ccnv crdg simplr simpr simpll infpssrlem5
      vex cres eqid ex exlimdv syl5bi imp3a sylbir exlimiv mpcom vtoclg anabsi7
      syl5 syl vtocl ) BDHZIZBVTJKZLZMVTNKZOZBAIZBAJKZLZMANKZODACVTAPZWCWHWDWIW
      JWAWFWBWGVTABUAVTABJQRVTAMNQUBWAWBWDWBBSTWEBVTJUCUDEHZVTIZWKVTJKZLZWDOZWE
      EBSWKBPZWNWCWDWPWLWAWMWBWKBVTUEWKBVTJUMRUFFDUGFEUGUHLZFUIZWNWDWLWRWMFWKVT
      UJUKWQWOFWQFHZVTWKULTZWOWSVTWKUNWTWLWMWDWLWKVTUOZWTWMWDOZWKVTUPWTXAXBWMWK
      VTGHZUQZGUIWTXALZWDWKVTGDVEURXEXDWDGXEXDWDXEXDLEFGXCUSWSUTMVFZDWTXAXDVAXE
      XDVBWTXAXDVCXFVGVDVHVIVJVHVQVKVLVMVNVOVRVPVS $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d F a b $.  $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.

    $( Taking images under a one-to-one function preserves subsets. $)
    f1imass $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C_ ( F " D ) <-> C C_ D ) ) $=
      ( va wf1 wss wa cima cv wcel wi simplrl sseld wb 3expa f1elima syl3anc ex
      simplr simplll simpr simp1rl simp1rr 3imtr3d pm2.43d ssrdv imass2 impbid1
      cfv syld ) ABEGZCAHZDAHZIZIZECJZEDJZHZCDHZUQUTVAUQUTIZFCDVBFKZCLZVCDLZVBV
      DVCALZVDVEMZVBCAVCUMUNUOUTNOVBVFVGVBVFIZVCEUKZURLZVIUSLZVDVEVHURUSVIUQUTV
      FUAOVHUMVFUNVJVDPUMUPUTVFUBZVBVFUCZUQUTVFUNUNUOUMUTVFUDQABEVCCRSVHUMVFUOV
      KVEPVLVMUQUTVFUOUNUOUMUTVFUEQABEVCDRSUFTULUGUHTCDEUIUJ $.
      $( [30-Oct-2014] $)

    $( Taking images under a one-to-one function preserves equality. $)
    f1imaeq $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) = ( F " D ) <-> C = D ) ) $=
      ( wf1 wss wa cima wceq f1imass wb ancom2s anbi12d eqss 3bitr4g ) ABEFZCAG
      ZDAGZHHZECIZEDIZGZUBUAGZHCDGZDCGZHUAUBJCDJTUCUEUDUFABCDEKQSRUDUFLABDCEKMN
      UAUBOCDOP $.
      $( [30-Oct-2014] $)

    $( Taking images under a one-to-one function preserves proper subsets. $)
    f1imapss $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C. ( F " D ) <-> C C. D ) ) $=
      ( wf1 wss wa cima wceq wpss f1imass f1imaeq notbid anbi12d dfpss2 3bitr4g
      wn ) ABEFCAGDAGHHZECIZEDIZGZTUAJZRZHCDGZCDJZRZHTUAKCDKSUBUEUDUGABCDELSUCU
      FABCDEMNOTUAPCDPQ $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d A x y f a b c $.  $d B x y f a b c $.

    $( Lemma for ~ infpssALT .  Dedekind infinite is a cardinal property. $)
    infpssen1 $p |- ( ( A ~~ B /\ B e. _V ) -> ( E. x ( x C. A /\ x ~~ A ) ->
      E. y ( y C. B /\ y ~~ B ) ) ) $=
      ( vb vf cen wbr cvv wcel wa cv wpss wex wi wceq breq2 anbi12d vex cima va
      relen brrelexi breq1 psseq2 exbidv imbi1d imbi12d wf1o bren simpr wf1 wss
      imbi2d wb f1of1 pssss ssid jctir f1imapss syl2an mpbird cdm imadmrn f1odm
      imaeq2d dff1o5 simprbi eqeq12d mpbii adantr psseq2d mpbid adantrr f1imaen
      crn simprr entr syl2anc f1oen2g mpan imaexg psseq1 cla4ev exlimdv exlimiv
      ax-mp ex sylbi vtocl2g adantrd sylan pm2.43i ) CDGHZDIJZKZALZCMZWQCGHZKZA
      NZBLZDMZXBDGHZKZBNZOZWNCIJZWOWPXGOCDGUBUCXHWOKWNXGWOUALZELZGHZWQXIMZWQXIG
      HZKZANZXBXJMZXBXJGHZKZBNZOZOCXJGHZXAXSOZOWNXGOUAECDIIXICPZXKYAXTYBXICXJGU
      DYCXOXAXSYCXNWTAYCXLWRXMWSXICWQUEXICWQGQRUFUGUHXJDPZYAWNYBXGXJDCGQYDXSXFX
      AYDXRXEBYDXPXCXQXDXJDXBUEXJDXBGQRUFUNUHXKXIXJFLZUIZFNXTXIXJFESUJYFXTFYFXN
      XSAYFXNXSYFXNKZYEWQTZXJMZYHXJGHZXSYFXLYIXMYFXLKZYHYEXITZMZYIYKYMXLYFXLUKY
      FXIXJYEULZWQXIUMZXIXIUMZKYMXLUOXLXIXJYEUPZXLYOYPWQXIUQZXIURUSXIXJWQXIYEUT
      VAVBYKYLXJYHYFYLXJPZXLYFYEYEVCZTZYEVPZPYSYEVDYFUUAYLUUBXJYFYTXIYEXIXJYEVE
      VFYFYNUUBXJPXIXJYEVGVHVIVJVKVLVMVNYGYHXIGHZXKYJYGYHWQGHZXMUUCYFXLUUDXMYFY
      NYOUUDXLYQYRXIXJWQYEASVOVAVNYFXLXMVQYHWQXIVRVSYFXKXNYEIJZYFXKFSZXIXJIYEVT
      WAVKYHXIXJVRVSXRYIYJKBYHUUEYHIJUUFYEWQIWBWGXBYHPXPYIXQYJXBYHXJWCXBYHXJGUD
      RWDVSWHWEWFWIWJWKWLWM $.
      $( [30-Oct-2014] $)

    $( Lemma for ~ infpssALT .  Dedekind finite sets have Dedekind finite
       subsets. $)
    infpssss $p |- ( ( A C_ B /\ B e. _V ) -> ( E. x ( x C. A /\ x ~~ A ) ->
      E. y ( y C. B /\ y ~~ B ) ) ) $=
      ( va vb vc wss cvv wcel wa cv wpss cen wbr wex wi wceq anbi12d wn imbi12d
      ssexg sseq1 psseq2 breq2 exbidv imbi1d sseq2 imbi2d psssstr pssssd ancoms
      cdif cun difss a1i unssd pssnel adantl simpll simprl sseldd simprr elndif
      wel ad2antrl wo ioran elun xchnxbir sylanbrc nelneq2 syl2anc eqcom sylnib
      ex exlimdv mpd dfpss2 adantrr cin c0 vex difexg ax-mp enref jctir ssinss1
      pssss inssdif0 sylib disjdif unen undif biimpi adantr breqtrd unex psseq1
      syl breq1 cla4ev vtocl2g adantrd sylancom pm2.43i ) CDHZDIJZKZALZCMZXJCNO
      ZKZAPZBLZDMZXODNOZKZBPZQZXGXHCIJZXIXTQCDIUBYAXHKXGXTXHELZFLZHZXJYBMZXJYBN
      OZKZAPZXOYCMZXOYCNOZKZBPZQZQCYCHZXNYLQZQXGXTQEFCDIIYBCRZYDYNYMYOYBCYCUCYP
      YHXNYLYPYGXMAYPYEXKYFXLYBCXJUDYBCXJNUESUFUGUAYCDRZYNXGYOXTYCDCUHYQYLXSXNY
      QYKXRBYQYIXPYJXQYCDXOUDYCDXONUESUFUIUAYDYGYLAYDYGYLYDYGKZXJYCYBUMZUNZYCMZ
      YTYCNOZYLYDYEUUAYFYDYEKZYTYCHYTYCRZTZUUAUUCXJYSYCYEYDXJYCHYEYDKXJYCXJYBYC
      UJUKULYSYCHUUCYCYBUOUPUQUUCGEVEZGAVEZTZKZGPZUUEYEUUJYDGXJYBURUSUUCUUIUUEG
      UUCUUIUUEUUCUUIKZYCYTRZUUDUUKGFVEGLZYTJZTZUULTUUKYBYCUUMYDYEUUIUTUUCUUFUU
      HVAVBUUKUUHUUMYSJZTZUUOUUCUUFUUHVCUUFUUQUUCUUHUUMYBYCVDVFUUGUUPVGUUHUUQKU
      UNUUGUUPVHUUMXJYSVIVJVKUUMYCYTVLVMYCYTVNVOVPVQVRYTYCVSVKVTYRYTYBYSUNZYCNY
      RYFYSYSNOZKXJYSWAWBRZYBYSWAWBRZKYTUURNOYRYFUUSYDYEYFVCYSYCIJYSIJFWCYCYBIW
      DWEZWFWGYRUUTUVAYRXJYCWAYBHZUUTYRXJYBHZUVCYEUVDYDYFXJYBWIVFXJYCYBWHWTXJYC
      YBWJWKYBYCWLWGXJYBYSYSWMVMYDUURYCRZYGYDUVEYBYCWNWOWPWQYKUUAUUBKBYTXJYSAWC
      UVBWRXOYTRYIUUAYJUUBXOYTYCWSXOYTYCNXASXBVMVPVQXCXDXEXF $.
      $( [30-Oct-2014] $)

    $( Lemma for ~ infpssALT . ` om ` is Dedekind infinite. $)
    infpssom $p |- ( om e. _V -> E. x ( x C. om /\ x ~~ om ) ) $=
      ( va vb com cvv wcel c0 wpss cen wbr wa cv csuc wi word syl con0 a1i wceq
      syl5ibrcom csn cdif wex difexg cuni eldifi wss peano2 ordom ordelss nnord
      mpan orduniss wb orduni vex uniex elon sylibr ordsssuc syl2anc sseldd wne
      mpbid peano3 eldifsn ordunisuc eqcomd adantl unieq eqeq2d wrex nnsuc nnon
      sylanbrc suceloni eleq1 imp simpr onsucuni2 ex rexlimiv sylbi adantr en3d
      suceq impbid peano1 cin wn disjsn con2bii disj4 bitr4i jctil psseq1 breq1
      mpbi anbi12d cla4egv sylc ) DEFZDGUAZUBZEFXDDHZXDDIJZKZALZDHZXHDIJZKZAUCD
      XCEUDZXBXFXEXBBCXDDBLZUEZCLZMZXLXMXDFZXNDFZNXBXQXMDFZXRXMDXCUFXSXMMZDXNXS
      XTDFZXTDUGZXMUHDOYAYBUIDXTUJULPXSXNXMUGZXNXTFZXSXMOZYCXMUKZXMUMPXSXNQFZYE
      YCYDUNXSXNOZYGXSYEYHYFXMUOPXNXMBUPUQURUSYFXNXMUTVAVDVBPRXODFZXPXDFZNXBYIX
      PDFXPGVCYJXOUHXOVEXPDGVFVORXQYIKZXMXPSZXOXNSZUNNXBYKYLYMYKYMYLXOXPUEZSZYI
      YOXQYIYNXOYIXOOYNXOSXOUKXOVGPVHVIYLXNYNXOXMXPVJVKTYKYLYMXMXNMZSZXQYQYIXQX
      SXMGVCKZYQXMDGVFYRYLCDVLYQCXMVMYLYQCDYIYLYQYIYLKZYPXMYSXMQFZYLYPXMSYIYLYT
      YIYTYLXPQFZYIXOQFUUAXOVNXOVPPXMXPQVQTVRYIYLVSXMXOVTVAVHWAWBPWCWDYMXPYPXMX
      OXNWFVKTWGRWEGDFZXEWHUUBDXCWIGSZWJXEUUCUUBDGWKWLUUCXEDXCWMWLWNWRWOXKXGAXD
      EXHXDSXIXEXJXFXHXDDWPXHXDDIWQWSWTXA $.
      $( [30-Oct-2014] $)

    infpssALT.a $e |- A e. _V $.
    $( A set with a denumerable subset has a proper subset equinumerous to it,
       proved without AC or Infinity. $)
    infpssALT $p |- ( om ~<_ A -> E. x ( x C. A /\ x ~~ A ) ) $=
      ( va vb vc com cdom wbr cv cen wss wa wex wpss domen cvv wcel wi mpd syl
      relen brrelexi infpssom vex infpssen1 mpan2 adantr simpr infpssss sylancl
      exlimiv sylbi ) GBHIGDJZKIZUNBLZMZDNAJZBOURBKIMANZDGBCPUQUSDUQEJZUNOUTUNK
      IMENZUSUOVAUPUOFJZGOVBGKIMFNZVAUOGQRVCGUNKUBUCFUDUAUOUNQRVCVASDUEFEGUNUFU
      GTUHUQUPBQRVAUSSUOUPUICEAUNBUJUKTULUM $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d Y z w u v $.

    $( Lemma for ~ dffin2-3 .  In a chain of sets, a maximal element is the
       union of the chain. $)
    fin23lem4 $p |- ( {C.} Or Y -> ( E. u e. Y A. v e. Y -. u C. v <->
        U. Y e. Y ) ) $=
      ( crpss wor cv wpss wn wral wrex cuni wcel w3a wss wa sorpssi syl elssuni
      wo wi anassrs sspss orel1 eqimss2 syl6com sylbi ax-1 jaoi ralimdva 3impia
      unissb sylibr 3ad2ant2 eqssd simp2 eqeltrd 3exp rexlimdv ssnpss rgen wceq
      weq psseq1 notbid ralbidv rcla4ev mpan2 impbid1 ) CDEZBFZAFZGZHZACIZBCJZC
      KZCLZVIVNVQBCVIVJCLZVNVQVIVRVNMZVPVJCVSVPVJVSVKVJNZACIZVPVJNVIVRVNWAVIVRO
      ZVMVTACWBVKCLZOVJVKNZVTSZVMVTTZVIVRWCWECVJVKPUAWDWFVTWDVLBAVBZSZWFVJVKUBV
      MWHWGVTVLWGUCVKVJUDUEUFVTVMUGUHQUIUJACVJUKULVRVIVJVPNVNVJCRUMUNVIVRVNUOUP
      UQURVQVPVKGZHZACIZVOWJACWCVKVPNWJVKCRVKVPUSQUTVNWKBVPCVJVPVAZVMWJACWLVLWI
      VJVPVKVCVDVEVFVGVH $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ dffin2-4 .  In a chain of sets, a minimal element is the
       intersection of the chain. $)
    fin23lem5 $p |- ( {C.} Or Y -> ( E. u e. Y A. v e. Y -. v C. u <->
        |^| Y e. Y ) ) $=
      ( crpss wor cv wpss wn wral wrex cint wcel w3a wss intss1 3ad2ant2 wa syl
      wo wi sorpssi anassrs ax-1 weq sspss orel1 eqimss2 syl6com sylbi ralimdva
      jaoi 3impia ssint sylibr eqssd simp2 eqeltrd 3exp ssnpss rgen wceq psseq2
      rexlimdv notbid ralbidv rcla4ev mpan2 impbid1 ) CDEZAFZBFZGZHZACIZBCJZCKZ
      CLZVIVNVQBCVIVKCLZVNVQVIVRVNMZVPVKCVSVPVKVRVIVPVKNVNVKCOPVSVKVJNZACIZVKVP
      NVIVRVNWAVIVRQZVMVTACWBVJCLZQVTVJVKNZSZVMVTTZVIVRWCWECVKVJUAUBVTWFWDVTVMU
      CWDVLABUDZSZWFVJVKUEVMWHWGVTVLWGUFVKVJUGUHUIUKRUJULAVKCUMUNUOVIVRVNUPUQUR
      VCVQVJVPGZHZACIZVOWJACWCVPVJNWJVJCOVPVJUSRUTVNWKBVPCVKVPVAZVMWJACWLVLWIVK
      VPVJVBVDVEVFVGVH $.
      $( [2-Nov-2014] $)
  $}

  ${
    $d Y z w b c $.  $d Y x y $.  $d Y d $.  $d d A b c $.  $d A x y b c $.
    $d Y u $.  $d A u $.  $d d u x y $.

    $( Lemma for ~ dffin2-2 .  The componentwise complement of a chain of sets
       is also a chain of sets. $)
    fin23lem6 $p |- ( {C.} Or Y -> {C.} Or { u e. ~P A | ( A \ u ) e. Y } ) $=
      ( vx vy crpss wor cv wss wo cdif wcel wral wa difeq2 eleq1d elrab syl2anb
      weq wi cpw crab an4 biimpi sorpssi expcom wceq vex elpw dfss4 bitri sscon
      sseq12 syl5ib ancoms orim12d com12 orcoms syl6 com3l imp3a syl5 ralrimivv
      wb sorpss sylibr ) CFGZDHZEHZIZVIVHIZJZEBAHZKZCLZABUAZUBZMDVQMVQFGVGVLDEV
      QVQVHVQLZVIVQLZNVHVPLZVIVPLZNZBVHKZCLZBVIKZCLZNZNZVGVLVRVTWDNZWAWFNZWHVSV
      OWDAVHVPADSVNWCCVMVHBOPQVOWFAVIVPAESVNWECVMVIBOPQWIWJNWHVTWDWAWFUCUDRVGWB
      WGVLWGVGWBVLWGVGWCWEIZWEWCIZJZWBVLTZVGWGWMCWCWEUEUFWLWKWNWBWLWKJZVLVTBWCK
      ZVHUGZBWEKZVIUGZWOVLTWAVTVHBIWQVHBDUHUIVHBUJUKWAVIBIWSVIBEUHUIVIBUJUKWQWS
      NZWLVJWKVKWLWPWRIWTVJWEWCBULWPVHWRVIUMUNWKWRWPIZWTVKWCWEBULWSWQXAVKVDWRVI
      WPVHUMUOUNUPRUQURUSUTVAVBVCDEVQVEVF $.
      $( [2-Nov-2014] $)
  $}

  ${
    $d a b c d e v u w x y z $.

    $( Lemma for ~ dffin2-2 .  The componentwise complement of a nonempty
       collection of sets is nonempty. $)
    fin23lem7 $p |- ( ( b e. ~P ~P a /\ b =/= (/) ) ->
      { c e. ~P a | ( a \ c ) e. b } =/= (/) ) $=
      ( vx cv cpw wcel c0 wne cdif crab wel wex n0 wss difss elpw2 wceq sylib
      wa vex mpbir elpwi sselda dfss4 simpr eqeltrd difeq2 eleq1d sylanbrc ne0i
      a1i elrab syl ex exlimdv syl5bi imp ) BEZAEZFZFGZUSHIZUTCEZJZUSGZCVAKZHIZ
      VCDBLZDMVBVHDUSNVBVIVHDVBVIVHVBVITZUTDEZJZVGGZVHVJVLVAGZUTVLJZUSGZVMVNVJV
      NVLUTOUTVKPVLUTAUAZQUBULVJVOVKUSVJVKUTOZVOVKRVJVKVAGVRVBUSVAVKUSVAUCUDVKU
      TVQQSVKUTUESVBVIUFUGVFVPCVLVAVDVLRVEVOUSVDVLUTUHUIUMUJVGVLUKUNUOUPUQUR $.
      $( [31-Oct-2014] $)

    $( Two ways to express overlapping subsets. $)
    pssdifcom1 $p |- ( ( A C_ C /\ B C_ C ) ->
      ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $=
      ( wss wa cdif wpss difcom a1i ssconb ancoms notbid anbi12d dfpss3 3bitr4g
      wn wb ) ACDZBCDZEZCAFZBDZBUADZPZECBFZADZAUEDZPZEUABGUEAGTUBUFUDUHUBUFQTCA
      BHITUCUGSRUCUGQBACJKLMUABNUEANO $.
      $( [31-Oct-2014] $)

    $( Two ways to express non-covering pairs of subsets. $)
    pssdifcom2 $p |- ( ( A C_ C /\ B C_ C ) ->
      ( B C. ( C \ A ) <-> A C. ( C \ B ) ) ) $=
      ( wss wa cdif wpss ssconb ancoms difcom a1i notbid anbi12d dfpss3 3bitr4g
      wn wb ) ACDZBCDZEZBCAFZDZUABDZPZEACBFZDZUEADZPZEBUAGAUEGTUBUFUDUHSRUBUFQB
      ACHITUCUGUCUGQTCABJKLMBUANAUENO $.
      $( [31-Oct-2014] $)

    ${
      $d ph u v x y $.  $d ps u v x y $.
      fin23lem11.a $e |- ( ( x C_ a /\ v C_ a ) -> ( [ ( a \ x ) / z ]
        [ v / w ] ps -> [ x / z ] [ ( a \ v ) / w ] ph ) ) $.
      $( Lemma for ~ dffin2-2 . $)
      fin23lem11 $p |- ( b e. ~P ~P a -> ( E. z e. { c e. ~P a | ( a \ c ) e. b
          }
        A. w e. { c e. ~P a | ( a \ c ) e. b } -. ph ->
          E. z e. b A. w e. b -. ps ) ) $=
        ( vy vu cv wcel wsb wn wral wa notbid ax-17 cpw cdif crab wi weq difeq2
        wrex eleq1d elrab w3a wsbc wel wss difss vex elpw2 mpbir a1i wceq elpwi
        simp2r sselda syl dfss4 sylib simpr eqeltrd 3ad2antl1 simpl3 cvv dfsbcq
        sylanbrc sbcbidv mpan2 rcla4va syl2anc simplrl con3d 3adantl3 ralrimiva
        adantlr mpd ralbidv rcla4ev 3exp syl5bi rexlimdv hbs1 hbn hbral sbequ12
        wb cbvral syl5bb cbvrex 3imtr4g ) HMZGMZUAZUANZAEKOZDCOZPZKWRIMZUBZWQNZ
        IWSUCZQZCXGUGBEFOZDLOZPZFWQQZLWQUGZAPZEXGQZDXGUGBPZEWQQZDWQUGWTXHXMCXGC
        MZXGNXRWSNZWRXRUBZWQNZRZWTXHXMUDXFYAIXRWSICUEXEXTWQXDXRWRUFUHUIWTYBXHXM
        WTYBXHUJZYAXIDXTUKZPZFWQQZXMWTXSYAXHVAYCYEFWQYCFHULZRZAEWRFMZUBZUKZDCOZ
        PZYEYHYJXGNZXHYMWTYBYGYNXHWTYGRZYJWSNZWRYJUBZWQNZYNYPYOYPYJWRUMWRYIUNYJ
        WRGUOZUPUQURYOYQYIWQYOYIWRUMZYQYIUSYOYIWSNZYTWTWQWSYIWQWSUTVBZYIWRUTVCY
        IWRVDVEWTYGVFVGXFYRIYJWSXDYJUSXEYQWQXDYJWRUFUHUIVLVHWTYBXHYGVIXCYMKYJXG
        KMZYJUSZXBYLUUDXRVJNXBYLWLCUOUUDXAYKDXRVJAEUUCYJVKVMVNSVOVPWTYBYGYMYEUD
        XHWTYBRYGRZYDYLUUEXRWRUMZYTYDYLUDUUEXSUUFWTXSYAYGVQXRWRUTVCUUEUUAYTWTYG
        UUAYBUUBWAYIWRYSUPVEJVPVRVSWBVTXLYFLXTWQLMZXTUSZXKYEFWQUUHXJYDXIDUUGXTV
        KSWCWDVPWEWFWGXOXHDCXGXOCTXCDKXGUUCXGNDTXBDXADCWHWIWJXOXAPZKXGQDCUEZXHX
        NUUIEKXGXNKTXAEAEKWHWIEKUEAXAAEKWKSWMUUJUUIXCKXGUUJXAXBXADCWKSWCWNWOXQX
        LDLWQXQLTXKDFWQYGDTXJDXIDLWHWIWJXQXIPZFWQQDLUEZXLXPUUKEFWQXPFTXIEBEFWHW
        IEFUEBXIBEFWKSWMUULUUKXKFWQUULXIXJXIDLWKSWCWNWOWP $.
        $( [31-Oct-2014] $)
    $}
  $}

  ${
    $d x y z w a b c d $.

    $( ` Fin2 ` expressed in terms of minimal elements. $)
    dffin2-2 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ {C.} Or y ) ->
        E. z e. y A. w e. y -. w C. z ) } $=
      ( va vb vc cv c0 wne crpss wor wa wpss wral wrex wcel wss wceq cvv wn cpw
      cfin2 wi cab w3a cdif crab simp2 ssrab2 vex pwex elpw2 mpbir simp1 simp3l
      a1i fin23lem7 syl2anc fin23lem6 adantl 3ad2ant3 neeq1 soeq2 anbi12d raleq
      rexeqbi1dv imbi12d rcla4va imp syl22anc wsb wsbc pssdifcom2 biimpd difexg
      ax-mp simpr simpl psseq12d sbc2ie 3imtr4g fin23lem11 sylc 3exp pssdifcom1
      weq ralrimiv impbii df-fin2 abeq2i pweq pweqd raleqdv elab 3bitr4i eqriv
      ) EUCBHZIJZWRKLZMZDHZCHZNZUAZDWROZCWRPZUDZBAHZUBZUBZOZAUEZFHZIJZXNKLZMZXC
      XBNZUAZDXNOZCXNPZUDZFEHZUBZUBZOZXHBYEOZYCUCQYCXMQYFYGYFXHBYEYFWRYEQZXAXGY
      FYHXAUFZYHXSDYCGHUGZWRQZGYDUHZOZCYLPZXGYFYHXAUIZYIYLYEQZYFYLIJZYLKLZYNYPY
      IYPYLYDRYKGYDUJYLYDYCEUKZULZUMUNUQYFYHXAUOYIYHWSYQYOYFYHWSWTUPEBGURUSXAYF
      YRYHWTYRWSGYCWRUTVAVBYPYFMYQYRMZYNYBUUAYNUDFYLYEXNYLSZXQUUAYAYNUUBXOYQXPY
      RXNYLIVCXNYLKVDVEXTYMCXNYLXSDXNYLVFVGVHVIVJVKXRXDACDFEBGXIYCRZXNYCRMZXNYC
      XIUGZNZXIYCXNUGZNZXDDFVLCUUEVMXRDUUGVMCAVLUUDUUFUUHXIXNYCVNVOXDUUFCDUUEXN
      YCTQZUUETQYSYCXITVPVQZFUKXCUUESZDFWGZMXBXNXCUUEUUKUULVRUUKUULVSVTWAXRUUHC
      DXIUUGAUKZUUIUUGTQYSYCXNTVPVQCAWGZXBUUGSZMXCXIXBUUGUUNUUOVSUUNUUOVRVTWAWB
      WCWDWEWHYGYBFYEYGXNYEQZXQYAYGUUPXQUFZUUPXEDYJXNQZGYDUHZOZCUUSPZYAYGUUPXQU
      IZUUQUUSYEQZYGUUSIJZUUSKLZUVAUVCUUQUVCUUSYDRUURGYDUJUUSYDYTUMUNUQYGUUPXQU
      OUUQUUPXOUVDUVBYGUUPXOXPUPEFGURUSXQYGUVEUUPXPUVEXOGYCXNUTVAVBUVCYGMUVDUVE
      MZUVAXHUVFUVAUDBUUSYEWRUUSSZXAUVFXGUVAUVGWSUVDWTUVEWRUUSIVCWRUUSKVDVEXFUU
      TCWRUUSXEDWRUUSVFVGVHVIVJVKXDXRACDBEFGUUCWRYCRMZUUEWRNZYCWRUGZXINZXRDBVLC
      UUEVMXDDUVJVMCAVLUVHUVIUVKXIWRYCWFVOXRUVICDUUEWRUUJBUKUUKDBWGZMXCUUEXBWRU
      UKUVLVSUUKUVLVRVTWAXDUVKCDXIUVJUUMUUIUVJTQYSYCWRTVPVQUUNXBUVJSZMXBUVJXCXI
      UUNUVMVRUUNUVMVSVTWAWBWCWDWEWHWIYFEUCEFCDWJWKXLYGAYCYSAEWGZXHBXKYEUVNXJYD
      XIYCWLWMWNWOWPWQ $.
      $( [2-Nov-2014] $)

    $( ` Fin2 ` sets contain unions for all nonempty chains. $)
    dffin2-3 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ {C.} Or y ) ->
        U. y e. y ) } $=
      ( va vz vw cfin2 cv c0 wne crpss wor wa cuni wcel wi cpw wral cab wpss wn
      wrex wb fin23lem4 adantl pm5.74i ralbii df-fin2 abeq2i vex weq pweq pweqd
      raleqdv elab 3bitr4i eqriv ) CFBGZHIZUQJKZLZUQMUQNZOZBAGZPZPZQZARZUTDGEGS
      TEUQQDUQUAZOZBCGZPZPZQZVBBVLQZVJFNVJVGNVIVBBVLUTVHVAUSVHVAUBUREDUQUCUDUEU
      FVMCFCBDEUGUHVFVNAVJCUIACUJZVBBVEVLVOVDVKVCVJUKULUMUNUOUP $.
      $( [2-Nov-2014] $)

    $( ` Fin2 ` sets contain intersections for all nonempty chains. $)
    dffin2-4 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ {C.} Or y ) ->
        |^| y e. y ) } $=
      ( va vw vz cfin2 cv c0 wne crpss wor wa cint wcel wi cpw wral cab wpss wn
      wrex fin23lem5 adantl pm5.74i ralbii dffin2-2 abeq2i vex weq pweq raleqdv
      wb pweqd elab 3bitr4i eqriv ) CFBGZHIZUQJKZLZUQMUQNZOZBAGZPZPZQZARZUTDGEG
      STDUQQEUQUAZOZBCGZPZPZQZVBBVLQZVJFNVJVGNVIVBBVLUTVHVAUSVHVAULURDEUQUBUCUD
      UEVMCFCBEDUFUGVFVNAVJCUHACUIZVBBVEVLVOVDVKVCVJUJUMUKUNUOUP $.
      $( [2-Nov-2014] $)

    $d a b c A $.  $d a b c B $.
    $( A subset of a II-finite set is II-finite. $)
    ssfin2 $p |- ( ( A e. Fin2 /\ B C_ A ) -> B e. Fin2 ) $=
      ( va vb vc cfin2 wcel cvv wa wss simpl cv wi wceq eleq1 cpw wral dffin2-3
      sspwb abeq2i ssexg ancoms sseq2 anbi12d imbi1d sseq1 anbi2d imbi12d crpss
      jca c0 wne wor cuni bitri ssralv sylbi 3imtr4g impcom vtocl2g mpcom ) AFG
      ZBHGZIVBBAJZIZBFGZVEVBVCVBVDKVDVBVCBAFUAUBUJCLZFGZDLZVGJZIZVIFGZMVBVIAJZI
      ZVLMVEVFMCDABFHVGANZVKVNVLVOVHVBVJVMVGAFOVGAVIUCUDUEVIBNZVNVEVLVFVPVMVDVB
      VIBAUFUGVIBFOUHVJVHVLVJELZUKULVQUIUMIVQUNVQGMZEVGPZPZQZVREVIPZPZQZVHVLVJW
      CVTJZWAWDMVJWBVSJWEVIVGSWBVSSUOVREWCVTUPUQWACFCERTWDDFDERTURUSUTVA $.
      $( [2-Nov-2014] $)
  $}

  $c seqom $.

  ${
    $( Extend class notation to include index-aware recursive definitions. $)
    cseqom $a class seqom ( F , I ) $.

    $d F i v $.  $d I i v $.

    $( Index-aware recursive definitions over ` om ` .  A mashup of ~ df-rdg
       and ~ df-seq , this allows for recursive definitions that use an index
       in the recursion in cases where Infinity is not admitted. $)
    df-seqom $a |- seqom ( F , I ) = ( rec ( ( i e. om , v e. _V |->
        <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. ) " om ) $.
  $}

  ${
    $d F a b c d $.  $d I a b c d $.

    $( Lemma for ` seqom ` .  Change bound variables. $)
    seqomlem0 $p |- rec ( ( a e. om , b e. _V |-> <. suc a , ( a F b ) >. ) ,
      <. (/) , ( _I ` I ) >. ) = rec ( ( c e. om , d e. _V |->
      <. suc c , ( c F d ) >. ) , <. (/) , ( _I ` I ) >. ) $=
      ( com cvv cv csuc co cop cmpt2 wceq c0 cid cfv crdg weq suceq oveq1 oveq2
      opeq12d opeq2d cbvmpt2v rdgeq1 ax-mp ) CDGHCIZJZUHDIZAKZLZMZEFGHEIZJZUNFI
      ZAKZLZMZNUMOBPQLZRUSUTRNCDEFGHULURUOUNUJAKZLCESUIUOUKVAUHUNTUHUNUJAUAUCDF
      SVAUQUOUJUPUNAUBUDUEUTUMUSUFUG $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d Q a b c i v $.  $d A a b i v $.  $d F a b i v $.  $d I a b $.
    seqomlem.a $e |- Q = rec ( ( i e. om , v e. _V |->
        <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. ) $.
    $( Lemma for ` seqom ` .  The underlying recursion generates a sequence of
       pairs with the expected first values. $)
    seqomlem1 $p |- ( A e. om -> ( Q ` A ) =
      <. A , ( 2nd ` ( Q ` A ) ) >. ) $=
      ( vb cv cfv c2nd cop wceq c0 fveq2 id fveq2d opeq12d eqeq12d opeq2d va co
      csuc weq cid com cvv cmpt2 crdg fveq1i opex rdg0 eqtri fvex eqcomi opeq2i
      0ex op2nd 3eqtr4a ax-mp wcel df-ov suceq oveq1 oveq2 ovmpt2 mpan2 syl5eqr
      eqid eqeq1d syl5ibrcom vex sucex ovex a1i syld con0 rdgsuc fveq2i 3eqtr4g
      nnon syl sylibrd finds ) UAIZCJZWEWFKJZLZMNCJZNWIKJZLZMZHIZCJZWMWNKJZLZMZ
      WMUCZCJZWRWSKJZLZMZBCJZBXCKJZLZMUAHBWENMZWFWIWHWKWENCOZXFWENWGWJXFPXFWFWI
      KXGQRSUAHUDZWFWNWHWPWEWMCOZXHWEWMWGWOXHPXHWFWNKXIQRSWEWRMZWFWSWHXAWEWRCOZ
      XJWEWRWGWTXJPXJWFWSKXKQRSWEBMZWFXCWHXEWEBCOZXLWEBWGXDXLPXLWFXCKXMQRSWINFU
      EJZLZMZWLWINDAUFUGDIZUCZXQAIZEUBZLZUHZXOUIZJXONCYCGUJXOYBNXNUKULUMXPXONXO
      KJZLWIWKXNYDNYDXNNXNUQFUEUNURUOUPXPPXPWJYDNWIXOKOTUSUTWMUFVAZWQWNYBJZWRYF
      KJZLZMZXBYEWQYFWRWMWOEUBZLZMZYIYEYLWQWPYBJZYKMYEYMWMWOYBUBZYKWMWOYBVBYEWO
      UGVAYNYKMWNKUNDAWMWOUFUGYAYKYBWRWMXSEUBZLDHUDXRWRXTYOXQWMVCXQWMXSEVDRXSWO
      MYOYJWRXSWOWMEVETYBVIWRYJUKVFVGVHWQYFYMYKWNWPYBOVJVKYEYIYLYKWRYKKJZLZMYEY
      JYPWRYJYPMYEYPYJWRYJWMHVLVMWMWOEVNURUOVOTYLYFYKYHYQYLPYLYGYPWRYFYKKOTSVKV
      PYEWSYFXAYHYEWRYCJZWMYCJZYBJZWSYFYEWMVQVAYRYTMWMWAXOWMYBVRWBWRCYCGUJWNYSY
      BWMCYCGUJVSVTZYEWTYGWRYEWSYFKUUAQTSWCWD $.
      $( [1-Nov-2014] $)

    $( Lemma for ` seqom ` . $)
    seqomlem2 $p |- ( Q " om ) Fn om $=
      ( va vb vc com wfn cvv cv wcel cfv wceq con0 wb cop c2nd cima cxp wss wbr
      wf weu wral dff3 wrex csuc co cmpt2 c0 crdg rdgfnon fneq1i mpbir fvelimab
      cid omsson mp2an seqomlem1 opelxpi mpan2 eqeltrd eleq1 syl5ibcom rexlimiv
      fvex sylbi ssriv weq wal wex df-br bitri wa adantl eqeq1d biimpd vex syl6
      opth1 fveq2 op2nd syl6req rexlimdva rcla4ev mpdan opeq2 eqeq2d syl5ibrcom
      rexbidv impbid syl5bb alrimiv eqeq2 bibi2d albidv cla4ev syl df-eu sylibr
      syli rgen mpbir2an dffn2 ) BJUAZJKJLXHUEZXIXHJLUBZUCGMZHMZXHUDZHUFZGJUGGH
      JLXHUHGXHXJXKXHNZXLBOZXKPZHJUIZXKXJNZBQKZJQUCZXOXRRXTCAJLCMZUJYBAMDUKSULZ
      UMEUSOSZUNZQKYDYCUOQBYEFUPUQZUTHQJXKBURVAXQXSHJXLJNZXPXJNXQXSYGXPXLXPTOZS
      ZXJAXLBCDEFVBYGYHLNYIXJNXPTVIXLYHJLVCVDVEXPXKXJVFVGVHVJVKXNGJXKJNZXMHIVLZ
      RZHVMZIVNZXNYJXMXLXKBOZTOZPZRZHVMZYNYJYRHXMIMZBOZXKXLSZPZIJUIZYJYQXMUUBXH
      NZUUDXKXLXHVOXTYAUUEUUDRYFUTIQJUUBBURVAVPYJUUDYQYJUUCYQIJYJYTJNZVQZUUCYOU
      UBPZYQUUCUUGIGVLZUUHUUGUUCYTUUATOZSZUUBPZUUIUUGUUCUULUUGUUAUUKUUBUUFUUAUU
      KPYJAYTBCDEFVBVRVSVTYTUUJXKXLIWAWCWBUUIUUCUUHUUIUUAYOUUBYTXKBWDZVSVTXDUUH
      YPUUBTOXLYOUUBTWDXKXLGWAHWAWEWFWBWGYJUUDYQUUAXKYPSZPZIJUIZYJYOUUNPZUUPAXK
      BCDEFVBUUOUUQIXKJUUIUUAYOUUNUUMVSWHWIYQUUCUUOIJYQUUBUUNUUAXLYPXKWJWKWMWLW
      NWOWPYMYSIYPYOTVIYTYPPZYLYRHUURYKYQXMYTYPXLWQWRWSWTXAXMHIXBXCXEXFJXHXGUQ
      $.
      $( [1-Nov-2014] $)

    $( Lemma for ` seqom ` . $)
    seqomlem3 $p |- ( ( Q " om ) ` (/) ) = ( _I ` I ) $=
      ( va c0 com cfv cid wceq cop wcel cv peano1 mp2an con0 wfn mpbir cima wbr
      wrex cvv csuc co cmpt2 crdg fveq1i opex eqtri fveq2 eqeq1d rcla4ev wss wb
      rdg0 rdgfnon fneq1i omsson fvelimab df-br seqomlem2 fvex fnbrfvb ) HBIUAZ
      JEKJZLZHVGVFUBZVIHVGMZVFNZVKGOZBJZVJLZGIUCZHINZHBJZVJLZVOPVQHCAIUDCOZUEVS
      AODUFMUGZVJUHZJVJHBWAFUIVJVTHVGUJUQUKVNVRGHIVLHLVMVQVJVLHBULUMUNQBRSZIRUO
      VKVOUPWBWARSVJVTURRBWAFUSTUTGRIVJBVAQTHVGVFVBTVFISVPVHVIUPABCDEFVCPIHVGVF
      EKVDVEQT $.
      $( [1-Nov-2014] $)

    $( Lemma for ` seqom ` . $)
    seqomlem4 $p |- ( A e. om -> ( ( Q " om ) ` suc A ) =
      ( A F ( ( Q " om ) ` A ) ) ) $=
      ( va com wcel cfv co wceq cop cv cvv con0 wfn wb sylibr csuc peano2 cmpt2
      cima wbr wrex c2nd c0 cid crdg rdgsuc syl fveq1i fveq2i 3eqtr4g seqomlem1
      nnon fveq2d df-ov fvex suceq oveq1 opeq12d oveq2 opeq2d eqid ovmpt2 mpan2
      fveq2 eqeq1d rcla4ev mpdan wss rdgfnon fneq1i mpbir omsson fvelimab mp2an
      df-br seqomlem2 fnbrfvb mpbird eqcomd oveq2d eqtrd syl5eqr 3eqtrd syl2anc
      opex mpan ovex sylancr ) BIJZBUAZCIUDZKBBWPKZELZMZWOWRWPUEZWNWOWRNZWPJZWT
      WNHOZCKZXAMZHIUFZXBWNWOIJZWOCKZXAMZXFBUBZWNXHBCKZDAIPDOZUAZXLAOZELZNZUCZK
      ZBXKUGKZNZXQKZXAWNWOXQUHFUIKNZUJZKZBYCKZXQKZXHXRWNBQJYDYFMBUQYBBXQUKULWOC
      YCGUMXKYEXQBCYCGUMUNUOWNXKXTXQABCDEFGUPZURWNYABXSXQLZXABXSXQUSWNYHWOBXSEL
      ZNZXAWNXSPJYHYJMXKUGUTZDABXSIPXPYJXQWOBXNELZNXLBMXMWOXOYLXLBVAXLBXNEVBVCX
      NXSMYLYIWOXNXSBEVDVEXQVFWOYIWJVGVHWNYIWRWOWNXSWQBEWNWQXSWNWQXSMZBXSWPUEZW
      NXTWPJZYNWNXDXTMZHIUFZYOWNXKXTMZYQYGYPYRHBIXCBMXDXKXTXCBCVIVJVKVLCQRZIQVM
      ZYOYQSYSYCQRYBXQVNQCYCGVOVPZVQHQIXTCVRVSTBXSWPVTTWPIRZWNYMYNSACDEFGWAZIBX
      SWPYKWBWKWCWDWEVEWFWGWHXEXIHWOIXCWOMXDXHXAXCWOCVIVJVKWIYSYTXBXFSUUAVQHQIX
      ACVRVSTWOWRWPVTTWNUUBXGWSWTSUUCXJIWOWRWPBWQEWLWBWMWC $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.

    $( Equality theorem for ` seqom ` . $)
    seqomeq12 $p |- ( ( A = B /\ C = D ) -> seqom ( A , C ) =
      seqom ( B , D ) ) $=
      ( va vb wceq com cvv cv co cop cmpt2 c0 cid cfv crdg cima cseqom wcel wa
      csuc oveq opeq2d 3ad2ant1 mpt2eq3dva fveq2 rdgeq12 syl2an imaeq1d 3eqtr4g
      df-seqom ) ABGZCDGZUAZEFHIEJZUBZUPFJZAKZLZMZNCOPZLZQZHREFHIUQUPURBKZLZMZN
      DOPZLZQZHRACSBDSUOVDVJHUMVAVGGVCVIGVDVJGUNUMEFHIUTVFUMUPHTUTVFGURITUMUSVE
      UQUPURABUCUDUEUFUNVBVHNCDOUGUDVCVIVAVGUHUIUJFEACULFEBDULUK $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d F a b c d $.  $d I a b c d $.  $d G a b c d $.  $d A a b c d $.
    seqom.a $e |- G = seqom ( F , I ) $.
    $( An index-aware recursive definition defines a function on the natural
       numbers. $)
    fnseqom $p |- G Fn om $=
      ( va vb vd vc com wfn cvv cv csuc co cop cmpt2 c0 cid cfv crdg cima eqtri
      seqomlem0 seqomlem2 cseqom df-seqom fneq1i mpbir ) BIJEFIKELZMUIFLANOPQCR
      SOTZIUAZIJGUJHACACEFHGUCUDIBUKBACUEUKDFEACUFUBUGUH $.
      $( [1-Nov-2014] $)

    $( Value of an index-aware recursive definition at 0. $)
    seqom0g $p |- ( I e. _V -> ( G ` (/) ) = I ) $=
      ( va vb vd vc cvv wcel c0 cfv cid com cv csuc co cop cmpt2 eqtri df-seqom
      crdg cima cseqom fveq1i seqomlem0 seqomlem3 fvi syl5eq ) CIJKBLZCMLZCUJKE
      FNIEOZPULFOAQRSKUKRUBZNUCZLUKKBUNBACUDUNDFEACUATUEGUMHACACEFHGUFUGTCIUHUI
      $.
      $( [1-Nov-2014] $)

    $( Value of an index-aware recursive definition at a successor. $)
    seqomsuc $p |- ( A e. om -> ( G ` suc A ) = ( A F ( G ` A ) ) ) $=
      ( va vb vd vc com wcel csuc cvv cv co cop cmpt2 cfv wceq fveq1i crdg cima
      c0 cid seqomlem0 seqomlem4 cseqom df-seqom eqtri oveq2i eqeq12i sylibr )
      AJKALZFGJMFNZLUNGNBOPQUCDUDRPUAZJUBZRZAAUPRZBOZSUMCRZAACRZBOZSHAUOIBDBDFG
      IHUEUFUTUQVBUSUMCUPCBDUGUPEGFBDUHUIZTVAURABACUPVCTUJUKUL $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.

    $( Lemma for ~ fin23 .  In a class of ordinals, each element is fully
       identified by those of its predecessors which also belong to the
       class. $)
    fin23lem24 $p |- ( ( ( Ord A /\ B C_ A ) /\ ( C e. B /\ D e. B ) ) ->
      ( ( C i^i B ) = ( D i^i B ) <-> C = D ) ) $=
      ( word wa wcel cin wceq wne sseldd ordelord syl2anc simpr sylanbrc adantr
      wn elin ordirr syl wss wo simpll simplr simprl ordtri3 necon2abid simplrl
      wb simprr inss1 sseli nsyl nelne1 necomd simplrr ex sylbird necon4d ineq1
      jaodan impbid1 ) AEZBAUAZFZCBGZDBGZFZFZCBHZDBHZICDIVICDVJVKVICDJZCDGZDCGZ
      UBZVJVKJZVICEZDEZVOVLUIVIVCCAGVQVCVDVHUCZVIBACVCVDVHUDZVEVFVGUEKACLMZVIVC
      DAGVRVSVIBADVTVEVFVGUJKADLMZVQVRFVOCDCDUFUGMVIVOVPVIVMVPVNVIVMFZVKVJWCCVK
      GZCVJGZQVKVJJWCVMVFWDVIVMNVEVFVGVMUHCDBROWCCCGZWEWCVQWFQVIVQVMWAPCSTVJCCC
      BUKULUMCVKVJUNMUOVIVNFZDVJGZDVKGZQVPWGVNVGWHVIVNNVEVFVGVNUPDCBROWGDDGZWIW
      GVRWJQVIVRVNWBPDSTVKDDDBUKULUMDVJVKUNMVAUQURUSCDBUTVB $.
      $( [1-Nov-2014] $)

    $( In a chain of finite sets, dominance and subset coincide. $)
    fincssdom $p |- ( ( A e. Fin /\ B e. Fin /\ ( A C_ B \/ B C_ A ) ) ->
        ( A ~<_ B <-> A C_ B ) ) $=
      ( cfn wcel wss wo w3a cdom wn csdm wa wpss simpl1 simpr simpl3 orel1 sylc
      wbr dfpss3 sylanbrc php3 syl2anc domnsym con2i syl6 con4d ssdomg 3ad2ant1
      ex wi impbid ) ACDZBCDZABEZBAEZFZGZABHRZUNUQUNURUQUNIZBAJRZURIUQUSUTUQUSK
      ZULBALZUTULUMUPUSMVAUOUSVBVAUSUPUOUQUSNZULUMUPUSOUNUOPQVCBASTABUAUBUIURUT
      ABUCUDUEUFULUMUNURUJUPABCUGUHUK $.
      $( [8-Nov-2014] $)

    $( Lemma for ~ fin23 .  In a chain of finite sets, equinumerousity is
       equivalent to equality. $)
    fin23lem25 $p |- ( ( A e. Fin /\ B e. Fin /\ ( A C_ B \/ B C_ A ) ) ->
      ( A ~~ B <-> A = B ) ) $=
      ( cfn wcel wss cen wbr wceq wn wi wa wpss dfpss2 csdm php3 sdomnen syl ex
      syl5bir exp3a wo w3a adantl eqcom notbii anbi2i bitri cvv brrelexi ensymg
      relsdom mtod adantr jaod 3impia con4d eqeng 3ad2ant1 impbid ) ACDZBCDZABE
      ZBAEZUAZUBZABFGZABHZVEVGVFUTVAVDVGIZVFIZJZUTVAKZVBVJVCVKVBVHVIVAVBVHKZVIJ
      UTVLABLZVAVIABMVAVMVIVAVMKABNGVIBAOABPQRSUCTVKVCVHVIUTVCVHKZVIJVAVNBALZUT
      VIVOVCBAHZIZKVNBAMVQVHVCVPVGBAUDUEUFUGUTVOVIUTVOKBANGZVIABOVRVFBAFGZBAPVR
      BUHDVFVSJBANUKUIABUHUJQULQRSUMTUNUOUPUTVAVGVFJVDABCUQURUS $.
      $( [1-Nov-2014] $)
  $}

  ${
    $d R x y a b $.  $d S x y a b $.  $d H x y a b $.  $d A x y a b $.
    $d B x y a b $.
    $( Infer isomorphism from one direction of an order proof for isomorphisms
       between strict orders. $)
    soisoi $p |- ( ( ( R Or A /\ S Po B ) /\ ( H : A -onto-> B /\
          A. x e. A A. y e. A ( x R y -> ( H ` x ) S ( H ` y ) ) ) ) ->
        H Isom R , S ( A , B ) ) $=
      ( va vb wa cv wbr cfv wi wral weq wcel wn fveq2 syl2anc wor wpo wf1o wiso
      wfo wb wf1 wf simprl fof syl wo simpll sotrieq con2bid sylan simprr breq1
      breq1d imbi12d breq2 breq2d rcla42va ancoms simpllr simplrl ffvelrn poirr
      wceq syl5ibrcom con2d syld ancom2s jaod sylbird con4d ralrimivva sylanbrc
      notbid dff13 df-f1o sotric po2nr imnan sylibr syl12anc impcon4bid df-iso
      ) CEUAZDFUBZJZCDGUEZAKZBKZELZWMGMZWNGMZFLZNZBCOACOZJZJZCDGUCZHKZIKZELZXDG
      MZXEGMZFLZUFZICOHCOCDEFGUDXBCDGUGZWLXCXBCDGUHZXGXHVIZHIPZNZICOHCOXKXBWLXL
      WKWLWTUIZCDGUJZUKXBXOHICCXBXDCQZXECQZJZJZXNXMYAXNRZXFXEXDELZULZXMRZXBWIXT
      YDYBUFWIWJXAUMZWIXTJZXNYDCXDXEEUNUOUPYAXFYEYCYAXFXIYEXBWTXTXFXINZWKWLWTUQ
      ZXTWTYHWSYHXDWNELZXGWQFLZNABXDXECCAHPZWOYJWRYKWMXDWNEURYLWPXGWQFWMXDGSUSU
      TBIPZYJXFYKXIWNXEXDEVAYMWQXHXGFWNXEGSVBUTVCVDUPZYAXMXIYAWJXHDQZXMXIRZNWIW
      JXAXTVEZYAXLXSYOYAWLXLWKWLWTXTVFXQUKZXBXRXSUQCDXEGVGTZWJYOJZYPXMXHXHFLZRZ
      DXHFVHZXMXIUUAXGXHXHFURVSVJTVKVLYAYCXHXGFLZYEXBWTXTYCUUDNZYIWTXSXRUUEXSXR
      JWTUUEWSUUEXEWNELZXHWQFLZNABXEXDCCAIPZWOUUFWRUUGWMXEWNEURUUHWPXHWQFWMXEGS
      USUTBHPZUUFYCUUGUUDWNXDXEEVAUUIWQXGXHFWNXDGSVBUTVCVDVMUPZYAXMUUDYAWJYOXMU
      UDRZNYQYSYTUUKXMUUBUUCXMUUDUUAXGXHXHFVAVSVJTVKVLVNVOVPVQHICDGVTVRXPCDGWAV
      RXBXJHICCYAXFXIYNYAXFRZXNYCULZYPXBWIXTUUMUULUFYFYGXFUUMCXDXEEWBUOUPYAXNYP
      YCYAWJYOXNYPNYQYSYTYPXNUUBUUCXNXIUUAXNXGXHXHFXDXEGSUSVSVJTYAYCUUDYPUUJYAW
      JYOXGDQZUUDYPNZYQYSYAXLXRUUNYRXBXRXSUICDXDGVGTWJYOUUNJJUUDXIJRUUODXHXGFWC
      UUDXIWDWEWFVLVNVOWGVQHICDEFGWHVR $.
      $( [2-Nov-2014] $)
  $}

  $( Strict dominance and elementhood are the same for finite ordinals. $)
  nnsdomel $p |- ( ( A e. om /\ B e. om ) -> ( A e. B <-> A ~< B ) ) $=
    ( com wcel wa ccrd cfv csdm wbr wceq wb cardnn eleq12 syl2an cfn cin onfin2
    con0 inss2 sseli eqsstri ficardsdom bitr3d ) ACDZBCDZEAFGZBFGZDZABDZABHIZUD
    UFAJUGBJUHUIKUEALBLUFAUGBMNUDAODBODUHUJKUECOACROPOQROSUAZTCOBUKTABUBNUC $.
    $( [2-Nov-2014] $)

  $( An ordinal with more elements of some type is larger. $)
  onsdominel $p |- ( ( A e. On /\ B e. On /\ ( A i^i C ) ~< ( B i^i C ) ) ->
      A e. B ) $=
    ( con0 wcel cin csdm wbr wa wn wb ontri1 ancoms wi cdom inex1g ssrin ssdomg
    wss cvv syl2im domnsym syl6 adantl sylbird con4d 3impia ) ADEZBDEZACFZBCFZG
    HZABEZUHUIIZUMULUNUMJZBASZULJZUIUHUPUOKBALMUIUPUQNUHUIUPUKUJOHZUQUIUKTEUPUK
    UJSURBCDPBACQUKUJTRUAUKUJUBUCUDUEUFUG $.
    $( [2-Nov-2014] $)

  ${
    $d F a $.  $d X a $.

    $( Two possibilities for the behavior of a function value. $)
    fvbr0 $p |- ( X F ( F ` X ) \/ ( F ` X ) = (/) ) $=
      ( va cv csn cima wcel weu cfv wbr c0 wceq wo cio wsbc iota4 eqcomi dfsbcq
      wb dffv3 ax-mp fvex eleq1 sbcie bitri biimpi elimasni 3syl orcd wn syl5eq
      iotanul olcd pm2.61i ) CDZABEFZGZCHZBBAIZAJZUSKLZMURUTVAURUQCUQCNZOZUSUPG
      ZUTUQCPVCVDVCUQCUSOZVDVBUSLVCVESUSVBCBATZQUQCVBUSRUAUQVDCUSBAUBUOUSUPUCUD
      UEUFABUSUGUHUIURUJZVAUTVGUSVBKVFUQCULUKUMUN $.
      $( [2-Nov-2014] $)

    $( The result of a function value is always a subset of the union of the
       range, even if it is invalid and thus empty. $)
    fvssunirn $p |- ( F ` X ) C_ U. ran F $=
      ( va cvv wcel cfv crn cuni wss cv wceq fveq2 sseq1d wbr c0 fvbr0 vex fvex
      wo mpbiri brelrn elssuni syl 0ss sseq1 jaoi ax-mp vtoclg wn fvprc pm2.61i
      ) BDEZBAFZAGZHZIZCJZAFZUOIZUPCBDUQBKURUMUOUQBALMUQURANZUROKZSUSAUQPUTUSVA
      UTURUNEUSUQURACQUQARUAURUNUBUCVAUSOUOIZUOUDZUROUOUETUFUGUHULUIZUPVBVCVDUM
      OUOBAUJMTUK $.
      $( [2-Nov-2014] $)
  $}

  ${
    $d i j a b c $.  $d S i j a b c $.  $d C a b c $.

    $( Lemma for ~ fin23lem22 . $)
    fin23lem26 $p |- ( ( ( S C_ om /\ -. S e. Fin ) /\ i e. om ) ->
      E. j e. S ( j i^i S ) ~~ i ) $=
      ( va vb cv com wcel wss cfn wn wa cin cen wbr wrex c0 wceq con0 syl breq2
      csuc rexbidv weq word ordom simpl 0fin eleq1 mpbiri necon3bi adantl tz7.5
      wne a1i syl3anc en0 incom eqeq1i bitri rexbii sylibr wi cdif cint simplrl
      difss omsson syl6ss syl5ss simplr ssel2 onfin2 eqsstri peano2 sseldi ssfi
      inss2 adantlr ex mtod ssdif0 necon3bbii sylib ad2ant2lr onint syl2anc csn
      cun simprr cvv vex en2sn mp2an simprl sseldd nnord wel ordirr inss1 sseli
      nsyl disjsn ad2antrr unen syl22anc wb ordsuc w3a simp2 simpl1 simpr eldif
      adantrr sylanbrc onnmin ee12an con4d imp simp3 sscon intss simpl2 ordelon
      ordsucss onmindif impbida df-suc eleq2i syl6bb expr pm5.32rd elin 3bitr4g
      sylan eqrdv indir syl6eq ineq1 breq1d snssi df-ss uneq2d ad2antrl 3brtr4d
      eqtrd rcla4ev rexlimdva cbvrexv syl6ib finds2 impcom ) BFZGHAGIZAJHZKZLZC
      FZAMZUUMNOZCAPZUVAUUSQNOZCAPZUUSDFZNOZCAPZUUSUVDUBZNOZCAPZUUQBDUUMQRUUTUV
      BCAUUMQUUSNUAUCBDUDUUTUVECAUUMUVDUUSNUAUCUUMUVGRUUTUVHCAUUMUVGUUSNUAUCUUQ
      AUURMZQRZCAPZUVCUUQGUEZUUNAQUNZUVLUVMUUQUFUOUUNUUPUGUUPUVNUUNUUOAQAQRUUOQ
      JHUHAQJUIUJUKULCGAUMUPUVBUVKCAUVBUUSQRUVKUUSUQUUSUVJQUURAURUSUTVAVBUVDGHZ
      UUQUVFUVIVCUVOUUQLZUVFEFZAMZUVGNOZEAPZUVIUVPUVEUVTCAUVPUURAHZUVEUVTUVPUWA
      UVELZLZAUURUBZVDZVEZAHUWFAMZUVGNOZUVTUWCUWEAUWFAUWDVGZUWCUWESIZUWEQUNZUWF
      UWEHUWCUWEASUWIUWCAGSUVOUUNUUPUWBVFZVHVIVJUUQUWAUWKUVOUVEUUQUWALZAUWDIZKU
      WKUWMUWNUUOUUNUUPUWAVKUWMUWDJHZUWNUUOVCUUNUWAUWOUUPUUNUWALUURGHZUWOAGUURV
      LUWPGJUWDGSJMJVMSJVRVNUURVOVPTVSUWOUWNUUOUWDAVQVTTWAUWNUWEQAUWDWBWCWDWEUW
      EWFWGVPUWCUUSUURWHZWIZUVDUVDWHZWIZUWGUVGNUWCUVEUWQUWSNOZUUSUWQMQRZUVDUWSM
      QRZUWRUWTNOUVPUWAUVEWJUXAUWCUURWKHUVDWKHUXACWLDWLUURUVDWKWKWMWNUOUWCUURUE
      ZUXBUWCUWPUXDUWCAGUURUWLUVPUWAUVEWOWPUURWQTZUXDUURUUSHZKUXBUXDCCWRUXFUURW
      SUUSUURUURUURAWTXAXBUUSUURXCVBTUVOUXCUUQUWBUVODDWRKZUXCUVOUVDUEUXGUVDWQUV
      DWSTUVDUVDXCVBXDUUSUVDUWQUWSXEXFUWCUWGUUSUWQAMZWIZUWRUWCUWGUURUWQWIZAMZUX
      IUWCEUWGUXKUWCUVQUWFHZUVQAHZLUVQUXJHZUXMLUVQUWGHUVQUXKHUWCUXMUXLUXNUVPUWB
      UXMUXLUXNXGUVPUWBUXMLZLZUXLUVQUWDHZUXNUXPUXMASIZUWDUEZUXLUXQXGUVPUWBUXMWJ
      UXPAGSUVOUUNUUPUXOVFVHVIUVPUWBUXSUXMUWCUXDUXSUXEUURXHWDXNUXMUXRUXSXIZUXLU
      XQUXTUXLUXQUXTUXQUXLUXTUWJUXQKZUVQUWEHZUXLKUXTUWEASUWIUXMUXRUXSXJVJUXTUYA
      UYBUXTUYALUXMUYAUYBUXMUXRUXSUYAXKUXTUYAXLUVQAUWDXMXOVTUWEUVQXPXQXRXSUXTUX
      QLZAUVQUBZVDZVEZUWFUVQUYCUWEUYEIZUYFUWFIUYCUYDUWDIZUYGUXTUXQUYHUXTUXSUXQU
      YHVCUXMUXRUXSXTZUVQUWDYETXSUYDUWDAYATUWEUYEYBTUYCUXRUVQSHZUVQUYFHUXMUXRUX
      SUXQYCUXTUXSUXQUYJUYIUWDUVQYDYOAUVQYFWGWPYGUPUWDUXJUVQUURYHYIYJYKYLUVQUWF
      AYMUVQUXJAYMYNYPUURUWQAYQYRUWAUXIUWRRUVPUVEUWAUXHUWQUUSUWAUWQAIUXHUWQRUUR
      AUUAUWQAUUBWDUUCUUDUUFUVGUWTRUWCUVDYHUOUUEUVSUWHEUWFAUVQUWFRUVRUWGUVGNUVQ
      UWFAYSYTUUGWGYKUUHUVSUVHECAECUDUVRUUSUVGNUVQUURAYSYTUUIUUJVTUUKUUL $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23lem22 . $)
    fin23lem23 $p |- ( ( ( S C_ om /\ -. S e. Fin ) /\ i e. om ) ->
      E! j e. S ( j i^i S ) ~~ i ) $=
      ( va com wss cfn wcel wa cv cin cen wbr wral wo wb sseldd con0 syl word
      wn wrex weq wi wreu fin23lem26 ensym entr sylan2 wceq simpl simprl onfin2
      vex inss2 eqsstri sseli inss1 ssfi sylancl simprr nnord ordtri2or2 syl2an
      syl2anc ssrin orim12i fin23lem25 ordom fin23lem24 mpanl1 bitrd ralrimivva
      syl3anc syl5ib ad2antrr ineq1 breq1d reu4 sylanbrc ) AEFZAGHUAZIBJZEHZICJ
      ZAKZWCLMZCAUBWGDJZAKZWCLMZIZCDUCZUDZDANCANZWGCAUEABCUFWAWNWBWDWAWMCDAAWKW
      FWILMZWAWEAHZWHAHZIZIZWLWJWGWCWILMWOWIWCBUNUGWFWCWIUHUIWSWOWFWIUJZWLWSWFG
      HZWIGHZWFWIFZWIWFFZOZWOWTPWSWEEHZXAWSAEWEWAWRUKZWAWPWQULQZXFWEGHWFWEFXAEG
      WEERGKGUMRGUOUPZUQWEAURWEWFUSUTSWSWHEHZXBWSAEWHXGWAWPWQVAQZXJWHGHWIWHFXBE
      GWHXIUQWHAURWHWIUSUTSWSWEWHFZWHWEFZOZXEWSXFXJXNXHXKXFWETWHTXNXJWEVBWHVBWE
      WHVCVDVEXLXCXMXDWEWHAVFWHWEAVFVGSWFWIVHVNETWAWRWTWLPVIEAWEWHVJVKVLVOVMVPW
      GWJCDAWLWFWIWCLWEWHAVQVRVSVT $.
      $( [1-Nov-2014] $)

    fin23lem22.b $e |- C = ( i e. om |-> U. { j e. S | ( j i^i S ) ~~ i } ) $.
    $( Lemma for ~ fin23 but could be used elsewhere if we find a good name for
       it.  Explicit construction of a bijection (actually an isomorphism, TODO
       prove this) between an infinite subset of ` om ` and ` om ` itself. $)
    fin23lem22 $p |- ( ( S C_ om /\ -. S e. Fin ) -> C : om -1-1-onto-> S ) $=
      ( va com wss cfn wcel wa cv cin cen wbr ccrd cfv syl wceq wb wn crab cuni
      wreu fin23lem23 reucl simpll simpr sseldd con0 onfin2 inss2 eqsstri sseli
      inss1 ssfi mpan2 ficardom 3syl cardnn eqcomd eqeq1d eqcom syl6bb ad2antrl
      simprr sylancl ficarden syl2anc adantrr ineq1 breq1d reuuni2 3bitrd f1o2d
      weq ) BGHZBIJUAZKZCFGBDLZBMZCLZNOZDBUBUCZFLZBMZPQZAEVSWBGJZKWCDBUDZWDBJBC
      DUEZWCDBUFRVSWEBJZKZWEGJZWEIJZWGGJZWLBGWEVQVRWKUGVSWKUHUIGIWEGUJIMIUKUJIU
      LUMZUNZWNWFIJZWOWNWFWEHZWRWEBUOZWEWFUPZUQWFURRUSVSWHWKKZKZWBWGSZWGWBPQZSZ
      WFWBNOZWEWDSZWHXDXFTVSWKWHXDXEWGSXFWHWBXEWGWHXEWBWBUTVAVBXEWGVCVDVEXCWRWB
      IJZXFXGTXCWNWSWRXCWMWNXCBGWEVQVRXBUGVSWHWKVFZUIWQRWTXAVGWHXIVSWKGIWBWPUNV
      EWFWBVHVIXCXGWDWESZXHXCWKWIXGXKTXJVSWHWIWKWJVJWCXGDBWEDFVPWAWFWBNVTWEBVKV
      LVMVIWDWEVCVDVNVO $.
      $( [1-Nov-2014] $)

    $( The mapping constructed in ~ fin23lem22 is in fact an isomorphism. $)
    fin23lem27 $p |- ( ( S C_ om /\ -. S e. Fin ) ->
        C Isom _E , _E ( om , S ) ) $=
      ( va vb com wcel wa cep cv wbr syl cin cen wreu adantrr breq1d wceq wn wi
      wss cfn wor wpo wfo cfv wral wiso word wwe ordom ordwe weso mp2b a1i sopo
      ax-mp poss mpi adantr wf1o fin23lem22 f1ofo wel crab cuni nnsdomel adantl
      csdm biimpd fin23lem23 weq ineq1 cbvreuv sylibr reuuni3 cvv adantrl reucl
      wb inex1g simprr vex ensym sdomentr syl12anc ensdomtr syl2anc expr omsson
      imp con0 simpll sseldd sseldi onsdominel 3expia 3syld simprl breq2 unieqd
      rabbidv fvmptg eleq12d sylibrd epel fvex epelc ralrimivva soisoi syl22anc
      3imtr4g ) BHUCZBUDIUAZJZHKUEZBKUFZHBAUGZFLZGLZKMZYAAUHZYBAUHZKMZUBZGHUIFH
      UIHBKKAUJXRXQHUKHKULXRUMHUNHKUOUPZUQXOXSXPXOHKUFZXSXRYIYHHKURUSBHKUTVAVBX
      QHBAVCXTABCDEVDHBAVENXQYGFGHHXQYAHIZYBHIZJZJZFGVFZYDYEIZYCYFYMYNDLZBOZYAP
      MZDBVGZVHZYQYBPMZDBVGZVHZIZYOYMYNYAYBVKMZYTBOZUUCBOZVKMZUUDYMYNUUEYLYNUUE
      WBXQYAYBVIVJVLXQYLUUEUUHXQYLUUEJJZUUFYAPMZYAUUGVKMZUUHXQYLUUJUUEYMCLZBOZY
      APMZCBQZUUJYMYRDBQZUUOXQYJUUPYKBFDVMRZUUNYRCDBCDVNZUUMYQYAPUULYPBVOZSZVPV
      QUUNYRUUJCDBUUTUULYTTUUMUUFYAPUULYTBVOSVRNRUUIUUGVSIZUUEYBUUGPMZUUKXQYLUV
      AUUEYMUUCBIZUVAYMUUADBQZUVCXQYKUVDYJBGDVMVTZUUADBWANZUUCBBWCNRXQYLUUEWDXQ
      YLUVBUUEYMUUGYBPMZUVBYMUUMYBPMZCBQZUVGYMUVDUVIUVEUVHUUACDBUURUUMYQYBPUUSS
      ZVPVQUVHUUAUVGCDBUVJUULUUCTUUMUUGYBPUULUUCBVOSVRNUUGYBGWEWFNRUVAUUEUVBJUU
      KYAYBUUGVSWGWMWHUUFYAUUGWIWJWKYMYTWNIZUUCWNIZUUHUUDUBYMHWNYTWLYMBHYTXOXPY
      LWOZYMUUPYTBIZUUQYRDBWANZWPWQYMHWNUUCWLYMBHUUCUVMUVFWPWQUVKUVLUUHUUDYTUUC
      BWRWSWJWTYMYDYTYEUUCYMYJUVNYDYTTXQYJYKXAUVOCYAYQUULPMZDBVGZVHZYTHBACFVNZU
      VQYSUVSUVPYRDBUULYAYQPXBXDXCEXEWJYMYKUVCYEUUCTXQYJYKWDUVFCYBUVRUUCHBACGVN
      ZUVQUUBUVTUVPUUADBUULYBYQPXBXDXCEXEWJXFXGFGXHYDYEYAAXIYBAXIXJXNXKFGHBKKAX
      LXM $.
      $( [2-Nov-2014] $)
  $}

  $c Fin3DS $.
  ${
    $( Extend class notation to include the class of III-finite sets
       (descending sequence version). $)
    cfin2ds $a class Fin3DS $.

    $d g a b $.

    $( A set satisfies the descending sequence condition iff every descending
       function from ` om ` is eventually constant. $)
    df-fin2ds $a |- Fin3DS = { g | A. a ( ( a : om --> ~P g /\
        A. b e. om ( a ` suc b ) C_ ( a ` b ) ) -> |^| ran a e. ran a ) } $.


    $d a b c d A $.  $d a b c d B $.
    $( A subset of a III-finite set is III-finite. $)
    ssfin3ds $p |- ( ( A e. Fin3DS /\ B C_ A ) -> B e. Fin3DS ) $=
      ( va vb vc vd cfin2ds wcel cvv wa wss cv wi wceq eleq1 com cpw wf cfv wal
      simpl ssexg ancoms jca sseq2 anbi12d imbi1d sseq1 anbi2d imbi12d csuc crn
      wral cint sspwb fss sylan2b expcom anim1d imim1d alimdv df-fin2ds 3imtr4g
      abeq2i impcom vtocl2g mpcom ) AGHZBIHZJVHBAKZJZBGHZVKVHVIVHVJUAVJVHVIBAGU
      BUCUDCLZGHZDLZVMKZJZVOGHZMVHVOAKZJZVRMVKVLMCDABGIVMANZVQVTVRWAVNVHVPVSVMA
      GOVMAVOUEUFUGVOBNZVTVKVRVLWBVSVJVHVOBAUHUIVOBGOUJVPVNVRVPPVMQZELZRZFLZUKW
      DSWFWDSKFPUMZJZWDULZUNWIHZMZETZPVOQZWDRZWGJZWJMZETZVNVRVPWKWPEVPWOWHWJVPW
      NWEWGWNVPWEVPWNWMWCKWEVOVMUOPWMWCWDUPUQURUSUTVAWLCGCEFVBVDWQDGDEFVBVDVCVE
      VFVG $.
      $( [4-Nov-2014] $)

  $}

  ${
    $d U i u a b c d $.  $d A i u a b $.  $d i u t a b c d $.  $d B i u a b $.
    fin23lem.a $e |- U = seqom ( ( i e. om , u e. _V |-> if ( ( ( t ` i ) i^i
      u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t ) $.
    $( The beginning of the proof proper that every II-finite set (every chain
       of subsets has a maximal element) is III-finite (has no denumerable
       collection of subsets).  The proof here is the only one I could find,
       from ~ http://matwbn.icm.edu.pl/ksiazki/fm/fm6/fm619.pdf p.94 (writeup
       by Tarski, credited to Kuratowski).  Translated into English and modern
       notation, the proof proceeds as follows (variables renamed for
       uniqueness):

       Suppose for a contradiction that ` A ` is a set which is II-finite but
       not III-finite.

       For any countable sequence of distinct subsets ` T ` of ` A ` , we can
       form a decreasing sequence of non-empty subsets ` ( U `` T ) ` by taking
       finite intersections of initial segments of ` T ` while skipping over
       any element of ` T ` which would cause the intersection to be empty.

       By II-finiteness (as ~ dffin2-4 ) this sequence contains its
       intersection, call it ` Y ` ; since by induction every subset in the
       sequence ` U ` is non-empty, the intersection must be non-empty.

       Suppose that an element ` X ` of ` T ` has non-empty intersection with
       ` Y ` .  Thus said element has a non-empty intersection with the
       corresponding element of ` U ` , therefore it was used in the
       construction of ` U ` and all further elements of ` U ` are subsets of
       ` X ` , thus ` X ` contains the ` Y ` .  That is, all elements of ` X `
       either contain ` Y ` or are disjoint from it.

       Since there are only two cases, there must exist an infinite subset of
       ` T ` which uniformly either contain ` Y ` or are disjoint from it.  In
       the former case we can create an infinite set by subtracting ` Y ` from
       each element.  In either case, call the result ` Z ` ; this is an
       infinite set of subsets of ` A ` , each of which is disjoint from ` Y `
       and contained in the union of ` T ` ; the union of ` Z ` is strictly
       contained in the union of ` T ` , because only the latter is a superset
       of the non-empty set ` Y ` .

       The preceeding four steps may be iterated a countable number of times
       starting from the assumed denumerable set of subsets to produce a
       denumerable sequence ` B ` of the ` T ` sets from each stage.  Great
       caution is required to avoid ~ ax-dc here; in particular an effective
       version of the pigeonhole principle (for aleph-null pigeons and 2 holes)
       is required.  Since a denumerable set of subsets is assumed to exist, we
       can conclude ` om e. _V ` without the axiom.

       This ` B ` sequence is strictly decreasing, thus it has no minimum,
       contradicting the first assumption.

       This first section is sedicated to the construction of ` U ` and its
       intersection.  First, the value of ` U ` at a successor. $)
    fin23lem12 $p |- ( A e. om -> ( U ` suc A ) = if ( ( ( t ` A ) i^i
        ( U ` A ) ) = (/) , ( U ` A ) , ( ( t ` A ) i^i ( U ` A ) ) ) ) $=
      ( com wcel csuc cfv cvv cv cin c0 wceq cif cmpt2 co eqeq1d ifbieq12d cuni
      seqomsuc fvex fveq2 ineq1d eqidd ineq2 eqid inex2 ifex ovmpt2 mpan2 eqtrd
      crn id1 ) CGHZCIDJCCDJZEAGKELZBLZJZALZMZNOZVAVBPZQZRZCUSJZUQMZNOZUQVHPZCV
      EDUSUNUAFUBUPUQKHVFVJOCDUCZEACUQGKVDVJVEVGVAMZNOZVAVLPURCOZVCVMVAVBVAVLVN
      VBVLNVNUTVGVAURCUSUDUEZSVNVAUFVOTVAUQOZVMVIVAVLUQVHVPVLVHNVAUQVGUGZSVPUOV
      QTVEUHVIUQVHVKUQVGVKUIUJUKULUM $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 .  Each step of ` U ` is a decrease. $)
    fin23lem13 $p |- ( A e. om -> ( U ` suc A ) C_ ( U ` A ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq cif fin23lem12 wss ssid inss2 sseq1
      ifboth mp2an a1i eqsstrd ) CGHZCIDJCBKJZCDJZLZMNZUGUHOZUGABCDEFPUJUGQZUEU
      GUGQZUHUGQZUKUGRUFUGSUIULUMUKUGUHUGUJUGTUHUJUGTUAUBUCUD $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23. ` U ` will never evolve to an empty set if it did not
       start with one. $)
    fin23lem14 $p |- ( ( A e. om /\ U. ran t =/= (/) ) ->
        ( U ` A ) =/= (/) ) $=
      ( va vb com cv c0 wne cfv wi wceq fveq2 neeq1d imbi2d eqnetrd adantr wcel
      crn cuni csuc weq cvv vex rnex uniex cin cif cmpt2 seqom0g a1i fin23lem12
      ax-mp wa iftrue simprr wn iffalse df-ne biimpri pm2.61ian ex imim2d finds
      id1 imp ) CIUABJZUBZUCZKLZCDMZKLZVMGJZDMZKLZNVMKDMZKLZNVMHJZDMZKLZNVMWAUD
      ZDMZKLZNVMVONGHCVPKOZVRVTVMWGVQVSKVPKDPQRGHUEZVRWCVMWHVQWBKVPWADPQRVPWDOZ
      VRWFVMWIVQWEKVPWDDPQRVPCOZVRVOVMWJVQVNKVPCDPQRVMVSVLKVSVLOZVMVLUFUAWKVKVJ
      BUGUHUIEAIUFEJVJMAJZUJZKOWLWMUKULDVLFUMUPUNVMVHSWAIUAZWCWFVMWNWCWFWNWCUQZ
      WEWAVJMWBUJZKOZWBWPUKZKWNWEWROWCABWADEFUOTWQWOWRKLWQWOUQWRWBKWQWRWBOWOWQW
      BWPURTWQWNWCUSSWQUTZWOUQWRWPKWSWRWPOWOWQWBWPVATWSWPKLZWOWTWSWPKVBVCTSVDSV
      EVFVGVI $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 . ` U ` is a monotone function. $)
    fin23lem15 $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) ->
        ( U ` A ) C_ ( U ` B ) ) $=
      ( vb va cv cfv wss csuc wceq fveq2 sseq1d weq com wcel wa ssid fin23lem13
      a1i wi ad2antrr sstr ex syl findsg ) HJZEKZDEKZLULULLZIJZEKZULLZUNMZEKZUL
      LZCEKZULLHICDUJDNUKULULUJDEOPHIQUKUOULUJUNEOPUJUQNUKURULUJUQEOPUJCNUKUTUL
      UJCEOPUMDRSZULUAUCUNRSZVATDUNLZTURUOLZUPUSUDVBVDVAVCABUNEFGUBUEVDUPUSURUO
      ULUFUGUHUI $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 . ` U ` ranges over the original set; in particular
       ` ran U ` is a set, although we do not assume here that ` U ` is. $)
    fin23lem16 $p |- U. ran U = U. ran t $=
      ( va vb crn cuni cv wss wcel cfv wceq com cvv c0 ax-mp peano1 mpan2 cmpt2
      unissb wrex wfn wb cin cif fnseqom fvelrnb wa 0ss fin23lem15 rnex seqom0g
      vex uniex syl6sseq sseq1 syl5ibcom rexlimiv sylbi fnfvelrn mp2an eqeltrri
      mprgbir elssuni eqssi ) CHZIZBJZHZIZVIVLKFJZVLKZFVHFVHVLUBVMVHLZGJZCMZVMN
      ZGOUCZVNCOUDZVOVSUEDAOPDJVJMAJZUFZQNWAWBUGUAZCVLEUHZGOVMCUIRVRVNGOVPOLZVQ
      VLKVRVNWEVQQCMZVLWEQOLZVQWFKZSWEWGUJQVPKWHVPUKABVPQCDEULTTVLPLWFVLNVKVJBU
      OUMUPWCCVLEUNRZUQVQVMVLURUSUTVAVEVLVHLVLVIKWFVLVHWIVTWGWFVHLWDSOQCVBVCVDV
      LVHVFRVG $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 .  By ` Fin3DS ` , ` U ` achieves its minimum ( ` X `
       in the synopsis above, but we will not be assigning a symbol here). $)
    fin23lem17 $p |- ( ( U. ran t e. Fin3DS /\ t : om -1-1-> _V ) ->
        |^| ran U e. ran U ) $=
      ( vb vc va cv crn wcel com cpw wf cfv wss wa wi cvv wceq cuni cfin2ds wal
      csuc wral cint wf1 rnex uniex wb pweq feq3 anbi1d imbi1d albidv df-fin2ds
      vex syl elab2 biimpi f1f dmfex sylancr wfn cin c0 cmpt2 fnseqom fnex mpan
      cif adantl simpl dffn3 mpbi pwuni fin23lem16 pweqi sseqtri fss fin23lem13
      mp2an rgen pm3.2i feq1 fveq1 sseq12d ralbidv anbi12d rneq eleq12d imbi12d
      a1i inteqd cla4gv 3imp syl3anc syl2an ) BIZJZUAZUBKZLXAMZFIZNZGIZUDZXDOZX
      FXDOZPZGLUEZQZXDJZUFZXMKZRZFUCZLSKZCJZUFZXSKZLSWSUGZXBXQLHIZMZXDNZXKQZXOR
      ZFUCXQHXAUBWTWSBUQZUHUIYCXATZYGXPFYIYFXLXOYIYEXEXKYIYDXCTYEXEUJYCXAUKYDXC
      LXDULURUMUNUOHFGUPUSUTYBWSSKLSWSNXRYHLSWSVALSSWSVBVCXQXRQZCSKZXQLXCCNZXGC
      OZXFCOZPZGLUEZQZYAXRYKXQCLVDZXRYKDALSDIWSOAIZVEZVFTYSYTVKVGCXAEVHZLSCVIVJ
      VLXQXRVMYQYJYLYPLXSCNZXSXCPYLYRUUBUUALCVNVOXSXSUAZMXCXSVPUUCXAABCDEVQVRVS
      LXSXCCVTWBYOGLABXFCDEWAWCWDWMYKXQYQYAXPYQYARFCSXDCTZXLYQXOYAUUDXEYLXKYPLX
      CXDCWEUUDXJYOGLUUDXHYMXIYNXGXDCWFXFXDCWFWGWHWIUUDXNXTXMXSUUDXMXSXDCWJZWNU
      UEWKWLWOWPWQWR $.
      $( [4-Nov-2014] $)

    $( Lemma for ~ fin23 .  The first set in ` U ` to see an input set is
       either contained in it or disjoint from it. $)
    fin23lem19 $p |- ( A e. om -> ( ( U ` suc A ) C_ ( t ` A ) \/
      ( ( U ` suc A ) i^i ( t ` A ) ) = (/) ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq wss cif wa wn wo fin23lem12 eqif incom
      biimpi ineq2 eqeq1d biimprd impcom syl5eq inss1 sseq1 mpbiri orim12i 3syl
      adantl orcomd ) CGHZCIDJZCBKJZLZMNZUQUROZUPUQURCDJZLZMNZVBVCPNZVDUQVBNZQZ
      VDRZUQVCNZQZSZUTVASABCDEFTVEVKVDUQVBVCUAUCVGUTVJVAVGUSURUQLZMUQURUBVFVDVL
      MNZVFVMVDVFVLVCMUQVBURUDUEUFUGUHVIVAVHVIVAVCUROURVBUIUQVCURUJUKUNULUMUO
      $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 . ` X ` is either contained in or disjoint from all
       input sets. $)
    fin23lem20 $p |- ( A e. om -> ( |^| ran U C_ ( t ` A ) \/ ( |^| ran U i^i
        ( t ` A ) ) = (/) ) ) $=
      ( com wcel crn cint csuc cfv wss cv cin c0 wceq wo wfn cvv cif cmpt2 cuni
      fnseqom peano2 fnfvelrn sylancr intss1 fin23lem19 sstr2 ssdisj ex orim12d
      syl sylc ) CGHZDIZJZCKZDLZMZUTCBNZLZMZUTVCOPQZRURVCMZURVCOPQZRUPUTUQHZVAU
      PDGSUSGHVHEAGTENVBLANZOZPQVIVJUAUBDVBIUCFUDCUEGUSDUFUGUTUQUHUNABCDEFUIVAV
      DVFVEVGURUTVCUJVAVEVGURUTVCUKULUMUO $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 . ` X ` is not empty.  We only need here that ` t `
       has at least one set in its range besides ` (/) ` ; the much stronger
       hypothesis here will serve as our induction hypothesis though. $)
    fin23lem21 $p |- ( ( U. ran t e. Fin3DS /\ t : om -1-1-> _V ) ->
        |^| ran U =/= (/) ) $=
      ( va cv crn wcel com cvv wa c0 wne wi cfv wceq ax-mp cen wbr cuni cfin2ds
      wf1 cint fin23lem17 wrex wfn wb cin cif fnseqom fvelrnb id1 csn cdif wf1o
      cmpt2 vex f1f1orn f1oen2g sylancr csdm cdom snfi isfinite1 relen brrelexi
      wn cfn ensymg syl con3d anim2d mpi brsdom sylibr sdomentr mpancom sdomdif
      rnex wex eldifsn elssuni ssn0 sylan sylbi exlimiv 3syl fin23lem14 syl2anr
      n0 wss neeq1 syl5ibcom rexlimdva syl5bi adantl mpd ) BGZHZUAZUBIZJKWSUCZL
      CHZUDZXDIZXEMNZABCDEUEXCXFXGOXBXFFGZCPZXEQZFJUFZXCXGCJUGXFXKUHDAJKDGWSPAG
      ZUIZMQXLXMUJUQCXAEUKFJXECULRXCXJXGFJXCXHJIZLXIMNZXJXGXNXNXAMNZXOXCXNUMXCJ
      WTSTZWTMUNZUOZMNZXPXCWSKIJWTWSUPXQBURZJKWSUSJWTKWSUTVAXQXRWTVBTZXTXRJVBTZ
      XQYBXQXRJVCTZXRJSTZVHZLZYCXQYDJXRSTZVHZLZYGXRVIIYJMVDXRVERXQYIYFYDXQYEYHX
      QJKIYEYHOJWTSVFVGXRJKVJVKVLVMVNXRJVOVPWTKIYCXQLYBOWSYAVTXRJWTKVQRVRXRWTVS
      VKXTXHXSIZFWAXPFXSWKYKXPFYKXHWTIZXHMNZLXPXHWTMWBYLXHXAWLYMXPXHWTWCXHXAWDW
      EWFWGWFWHABXHCDEWIWJXIXEMWMWNWOWPWQWR $.
      $( [1-Nov-2014] $)

    $d P w z a b x $.  $d U v z $.  $d a b t v z $.  $d R b v i u a $.
    fin23lem.b $e |- P = { v e. om | |^| ran U C_ ( t ` v ) } $.
    fin23lem.c $e |- Q = ( w e. om |-> U. { x e. P | ( x i^i P ) ~~ w } ) $.
    fin23lem.d $e |- R = ( w e. om |-> U. { x e. ( om \ P ) |
        ( x i^i ( om \ P ) ) ~~ w } ) $.
    fin23lem.e $e |- Z = if ( P e. Fin , ( t o. R ) ,
        ( ( z e. P |-> ( ( t ` z ) \ |^| ran U ) ) o. Q ) ) $.
    $( Lemma for ~ fin23 .  The residual is also one-to-one.  This preserves
       the induction invariant. $)
    fin23lem28 $p |- ( t : om -1-1-> _V -> Z : om -1-1-> _V ) $=
      ( com cvv wcel va vb cv wf1 cfn ccom wceq wa wn cfv crn cint cdif cmpt wo
      cif eqif mpbi wf1o wss difss ominf cun crab ssrab2 eqsstri unfi syl5eqelr
      undif ex mtoi fin23lem22 sylancr adantl f1of1 f1ss mpan2 3syl f1co syldan
      f1eq1 syl5ibrcom impr wf weq wral fvex difexg ax-mp rgenw eqid fmpt fveq2
      wi a1i difeq1d fvmpt ad2antrl ad2antll eqeq12d uneq2 sseq2d simprbi sylib
      elrab2 syl5ib wb sseli anim12i f1fveq sylan2 sylibd sylbid dff13 sylanbrc
      ralrimivva syl mpan syl2an jaodan ) RSFUCZUDZGUETZLYAIUFZUGZUHZYCUIZLBGBU
      CZYAUJZJUKULZUMZUNZHUFZUGZUHZUOZRSLUDZLYCYDYMUPUGYPQYCLYDYMUQURYBYFYQYOYB
      YCYEYQYBYCUHZYQYERSYDUDZYBYCRRIUDZYSYRRRGUMZIUSZRUUAIUDZYTYCUUBYBYCUUARUT
      ZUUAUETZUIUUBRGVAZYCUUERUETZVBYCUUEUUGYCUUEUHRGUUAVCZUEGRUTZUUHRUGGYJDUCZ
      YAUJZUTZDRVDRNUULDRVEVFZGRVIURGUUAVGVHVJVKIUUACAPVLVMVNRUUAIVOUUCUUDYTUUF
      RUUARIVPVQVRRRSYAIVSVTRSLYDWAWBWCYBYGYNYQYBYGUHYQYNRSYMUDZYBGSYLUDZRGHUDZ
      UUNYGYBGSYLWDZUAUCZYLUJZUBUCZYLUJZUGZUAUBWEZWNZUBGWFUAGWFUUOUUQYBYKSTZBGW
      FUUQUVEBGYISTUVEYHYAWGYIYJSWHWIWJBGSYKYLYLWKZWLURWOYBUVDUAUBGGYBUURGTZUUT
      GTZUHZUHZUVBUURYAUJZYJUMZUUTYAUJZYJUMZUGZUVCUVJUUSUVLUVAUVNUVGUUSUVLUGYBU
      VHBUURYKUVLGYLBUAWEYIUVKYJYHUURYAWMWPUVFUVKSTUVLSTUURYAWGUVKYJSWHWIWQWRUV
      HUVAUVNUGYBUVGBUUTYKUVNGYLBUBWEYIUVMYJYHUUTYAWMWPUVFUVMSTUVNSTUUTYAWGUVMY
      JSWHWIWQWSWTUVJUVOUVKUVMUGZUVCUVOYJUVLVCZYJUVNVCZUGUVJUVPUVLUVNYJXAUVJUVQ
      UVKUVRUVMUVJYJUVKUTZUVQUVKUGUVGUVSYBUVHUVGUURRTZUVSUULUVSDUURRGDUAWEUUKUV
      KYJUUJUURYAWMXBNXEXCWRYJUVKVIXDUVJYJUVMUTZUVRUVMUGUVHUWAYBUVGUVHUUTRTZUWA
      UULUWADUUTRGDUBWEUUKUVMYJUUJUUTYAWMXBNXEXCWSYJUVMVIXDWTXFUVIYBUVTUWBUHUVP
      UVCXGUVGUVTUVHUWBGRUURUUMXHGRUUTUUMXHXIRSUURUUTYAXJXKXLXMXPUAUBGSYLXNXOUU
      IYGUUPUUMUUIYGUHRGHUSUUPHGCAOVLRGHVOXQXRRGSYLHVSXSRSLYMWAWBWCXTVQ $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ fin23 .  The residual is built from the same elements as the
       previous sequence. $)
    fin23lem29 $p |- U. ran Z C_ U. ran t $=
      ( va crn wss cfn wcel cv ccom cfv cint cdif cmpt cif wceq wa wn cuni eqif
      wo biimpi rncoss uniss ax-mp rneq unieqd sseq1d mpbiri adantl unissb wrex
      cab abid difss fvssunirn a1i syl5ss sseq1 syl5ibrcom rexlimiv sylbi rnmpt
      eqid eleq2s mprgbir sstri jaoi mp2b ) LGUAUBZFUCZIUDZBGBUCZWEUEZJSUFZUGZU
      HZHUDZUIUJZWDLWFUJZUKZWDULZLWLUJZUKZUOZLSZUMZWESZUMZTZQWMWSWDLWFWLUNUPWOX
      DWRWNXDWDWNXDWFSZUMZXCTZXEXBTXGWEIUQXEXBURUSWNXAXFXCWNWTXELWFUTVAVBVCVDWQ
      XDWPWQXDWLSZUMZXCTXIWKSZUMZXCXHXJTXIXKTWKHUQXHXJURUSXKXCTRUCZXCTZRXJRXJXC
      VEXMXLXLWJUJZBGVFZRVGZXJXLXPUBXOXMXORVHXNXMBGWGGUBZXMXNWJXCTXQWJWHXCWHWIV
      IWHXCTXQWEWGVJVKVLXLWJXCVMVNVOVPBRGWJWKWKVRVQVSVTWAWQXAXIXCWQWTXHLWLUTVAV
      BVCVDWBWC $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ fin23 .  The residual is disjoint from the common set. $)
    fin23lem30 $p |- ( Fun t -> ( U. ran Z i^i |^| ran U ) = (/) ) $=
      ( wcel wceq com va vb cfn cv ccom cfv crn cint cdif cmpt cif wa wfun cuni
      wn wo cin c0 wi eqif biimpi wral cdm wrex wb simpr cen crab funmpt funeqi
      wbr mpbir funco sylancl elunirn syl dmcoss simplr a1i fvco syl3anc eleq2d
      sseli incom wss wf wf1o difss ominf cun eqsstri undif mpbi unfi syl5eqelr
      ssrab2 ex mtoi ad2antrr fin23lem22 sylancr eleqtrd ffvelrn syl2anc eldifn
      f1of eleq2i sylnib sseldi fveq2 sseq2d elrab3 mtbid fin23lem20 orel1 sylc
      fdm syl5eq disj ra4 3syl sylbid syl5 rexlimdv ralrimiv sylibr rneq unieqd
      ineq1d eqeq1d syl5ibr exp3a impcom rncoss uniss ax-mp cab wel wex eluniab
      eleq2 syl6bi exlimiv sylbi eqid rnmpt unieqi eleq2s mprgbir ssdisj syl6eq
      rexlimivw mp2an a1d adantl jaoi mp2b ) LGUCRZFUDZIUEZBGBUDUUSUFZJUGUHZUIZ
      UJZHUEZUKSZUURLUUTSZULZUURUOZLUVESZULZUPZUUSUMZLUGZUNZUVBUQZURSZUSZQUVFUV
      LUURLUUTUVEUTVAUVHUVRUVKUVGUURUVRUVGUURUVMUVQUURUVMULZUVQUVGUUTUGZUNZUVBU
      QZURSZUVSUAUDZUVBRUOZUAUWAVBUWCUVSUWEUAUWAUVSUWDUWARZUWDUBUDZUUTUFZRZUBUU
      TVCZVDZUWEUVSUUTUMZUWFUWKVEUVSUVMIUMZUWLUURUVMVFUWMCTAUDTGUIZUQCUDVGVKAUW
      NVHUNZUJZUMCTUWOVIIUWPPVJVLZUUSIVMVNUBUWDUUTVOVPUVSUWIUWEUBUWJUWGUWJRUWGI
      VCZRZUVSUWIUWEUSZUWJUWRUWGUUSIVQWCUVSUWSUWTUVSUWSULZUWIUWDUWGIUFZUUSUFZRZ
      UWEUXAUWHUXCUWDUXAUVMUWMUWSUWHUXCSUURUVMUWSVRUWMUXAUWQVSUVSUWSVFZUWGUUSIV
      TWAWBUXAUXCUVBUQZURSZUWEUAUXCVBZUXDUWEUSUXAUXFUVBUXCUQZURUXCUVBWDUXAUVBUX
      CWEZUOUXJUXIURSZUPZUXKUXAUXBUVBDUDZUUSUFZWEZDTVHZRZUXJUXAUXBGRZUXQUXAUXBU
      WNRZUXRUOUXATUWNIWFZUWGTRUXSUXATUWNIWGZUXTUXAUWNTWEUWNUCRZUOZUYATGWHZUURU
      YCUVMUWSUURUYBTUCRZWIUURUYBUYEUURUYBULTGUWNWJZUCGTWEUYFTSGUXPTNUXODTWPWKG
      TWLWMGUWNWNWOWQWRWSIUWNCAPWTXATUWNIXFVPZUXAUWGUWRTUXEUXAUXTUWRTSUYGTUWNIX
      QVPXBTUWNUWGIXCXDZUXBTGXEVPGUXPUXBNXGXHUXAUXBTRZUXQUXJVEUXAUWNTUXBUYDUYHX
      IZUXOUXJDUXBTUXMUXBSUXNUXCUVBUXMUXBUUSXJXKXLVPXMUXAUYIUXLUYJEFUXBJKMXNVPU
      XJUXKXOXPXRUXGUXHUAUXCUVBXSVAUWEUAUXCXTYAYBWQYCYDYBYEUAUWAUVBXSYFUVGUVPUW
      BURUVGUVOUWAUVBUVGUVNUVTLUUTYGYHYIYJYKYLYMUVJUVRUVIUVJUVQUVMUVJUVPUVEUGZU
      NZUVBUQZURUVJUVOUYLUVBUVJUVNUYKLUVEYGYHYIUYLUVDUGZUNZWEZUYOUVBUQURSZUYMUR
      SUYKUYNWEUYPUVDHYNUYKUYNYOYPUYQUWEUAUYOUAUYOUVBXSUWEUWDUWGUVCSZBGVDZUBYQZ
      UNZUYOUWDVUARUAUBYRZUYSULZUBYSUWEUYSUBUWDYTVUCUWEUBUYSVUBUWEUYRVUBUWEUSBG
      UYRVUBUWDUVCRUWEUWGUVCUWDUUAUWDUVAUVBXEUUBUULYMUUCUUDUYNUYTBUBGUVCUVDUVDU
      UEUUFUUGUUHUUIUYLUYOUVBUUJUUMUUKUUNUUOUUPUUQ $.
      $( [2-Nov-2014] $)

    $d Z a b c $.  $d U a b c $.  $d G a b c t $.

    $( Lemma for ~ fin23 .  The residual is has a strictly smaller range than
       the previous sequence.  This will be iterated to build an unbounded
       chain. $)
    fin23lem31 $p |- ( ( t : om -1-1-> _V /\ G e. Fin3DS /\
        U. ran t C_ G ) -> U. ran Z C. U. ran t ) $=
      ( com c0 va cvv cv wf1 cfin2ds wcel crn cuni wss wpss ssfin3ds fin23lem29
      wa wne a1i cint wex fin23lem21 ancoms n0 sylib cdm wfn wceq cfv cin cmpt2
      cif fnseqom fndm ax-mp peano1 ne0i eqnetri dm0rn0 necon3bii mpbi intssuni
      wn fin23lem16 sseqtri sseli adantl wral wfun f1fun adantr fin23lem30 disj
      wi syl biimpi ra4 3syl con2d imp nelne1 syl2anc necomd exlimdv mpd df-pss
      ex sylanbrc sylan2 3impb ) SUBFUCZUDZLUEUFZXGUGUHZLUIZMUGUHZXJUJZXIXKUMXH
      XJUEUFZXMLXJUKXHXNUMZXLXJUIZXLXJUNZXMXPXOABCDEFGHIJKMNOPQRULUOXOUAUCZJUGZ
      UPZUFZUAUQZXQXOXTTUNZYBXNXHYCEFJKNURUSUAXTUTVAXOYAXQUAXOYAXQXOYAUMZXJXLYD
      XRXJUFZXRXLUFZVSZXJXLUNYAYEXOXTXJXRXTXSUHZXJXSTUNZXTYHUIJVBZTUNYIYJSTJSVC
      YJSVDKESUBKUCXGVEEUCZVFZTVDYKYLVHVGJXJNVISJVJVKTSUFSTUNVLSTVMVKVNYJTXSTJV
      OVPVQXSVRVKEFJKNVTWAWBWCXOYAYGXOYFYAXOXLXTVFTVDZYAVSZUAXLWDZYFYNWJXOXGWEZ
      YMXHYPXNSUBXGWFWGABCDEFGHIJKMNOPQRWHWKYMYOUAXLXTWIWLYNUAXLWMWNWOWPXRXJXLW
      QWRWSXCWTXAXLXJXBXDXEXF $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ fin23 .  Wrap the previous construction into a function to
       hide the hypotheses. $)
    fin23lem32 $p |- ( G e. Fin3DS -> E. a A. b
        ( ( b : om -1-1-> _V /\ U. ran b C_ G ) ->
        ( ( a ` b ) : om -1-1-> _V /\ U. ran ( a ` b ) C. U. ran b ) ) ) $=
      ( cfin2ds wcel com cvv cv wf1 crn cuni wss wa cfv wpss wi wal wex cmap co
      cpw cmpt wceq wb wf wfn dffn3 sylib ad2antrl sspwuni biimpri ad2antll fss
      f1fn syl2anc pwexg adantr vex f1f dmfex sylancr elmapg fin23lem28 syl fex
      mpbird fvmpt2 f1eq1 unieqd psseq1d anbi12d simprl simpl simprr fin23lem31
      eqid rneq syl3anc mpbir2and ex alrimiv ovex mptex ax17el hbeq fveq1 rneqd
      hbmpt1 imbi2d albid cla4ev weq sseq1d fveq2 psseq12d imbi12d cbvalv exbii
      sylibr ) LUAUBZUCUDFUEZUFZXRUGZUHZLUIZUJZUCUDXRNUEZUKZUFZYEUGZUHZYAULZUJZ
      UMZFUNZNUOZUCUDOUEZUFZYNUGZUHZLUIZUJZUCUDYNYDUKZUFZYTUGZUHZYQULZUJZUMZOUN
      ZNUOXQYCUCUDXRFLURZUCUPUQZMUSZUKZUFZUUKUGZUHZYAULZUJZUMZFUNZYMXQUUQFXQYCU
      UPXQYCUJZUUPUCUDMUFZMUGZUHZYAULZUUSUUKMUTZUUPUUTUVCUJVAUUSXRUUIUBZMUDUBZU
      VDUUSUVEUCUUHXRVBZUUSUCXTXRVBZXTUUHUIZUVGXSUVHXQYBXSXRUCVCUVHUCUDXRVKUCXR
      VDVEVFYBUVIXQXSUVIYBXTLVGVHVIUCXTUUHXRVJVLUUSUUHUDUBZUCUDUBZUVEUVGVAXQUVJ
      YCLUAVMVNXSUVKXQYBXSXRUDUBUCUDXRVBUVKFVOUCUDXRVPUCUDUDXRVQVRVFZUUHUCXRUDU
      DVSVLWCUUSUCUDMVBZUVKUVFUUSUUTUVMXSUUTXQYBABCDEFGHIJKMPQRSTVTVFZUCUDMVPWA
      UVLUCUDUDMWBVLFUUIMUDUUJUUJWMWDVLUVDUULUUTUUOUVCUCUDUUKMWEUVDUUNUVBYAUVDU
      UMUVAUUKMWNWFWGWHWAUVNUUSXSXQYBUVCXQXSYBWIXQYCWJXQXSYBWKABCDEFGHIJKLMPQRS
      TWLWOWPWQWRYLUURNUUJFUUIMUUHUCUPWSWTYDUUJUTZYKUUQFFOOYDUUJONFXAFOUUIMXEXB
      UVOYJUUPYCUVOYFUULYIUUOUVOYEUUKUTYFUULVAXRYDUUJXCZUCUDYEUUKWEWAUVOYHUUNYA
      UVOYGUUMUVOYEUUKUVPXDWFWGWHXFXGXHWAUUGYLNUUFYKOFOFXIZYSYCUUEYJUVQYOXSYRYB
      UCUDYNXRWEUVQYQYALUVQYPXTYNXRWNWFZXJWHUVQUUAYFUUDYIUVQYTYEUTUUAYFVAYNXRYD
      XKZUCUDYTYEWEWAUVQUUCYHYQYAUVQUUBYGUVQYTYEUVSXDWFUVRXLWHXMXNXOXP $.
      $( [2-Nov-2014] $)

  $}

  ${
    $d G a b c d e f g h i j k l m $.
    $( Lemma for ~ fin23 .  Discharge hypotheses. $)
    fin23lem33 $p |- ( G e. Fin3DS -> E. a A. b
        ( ( b : om -1-1-> _V /\ U. ran b C_ G ) ->
        ( ( a ` b ) : om -1-1-> _V /\ U. ran ( a ` b ) C. U. ran b ) ) ) $=
      ( vh vi vg vf vd vj vk vl vc com cv cfv cin c0 wceq cif eqid ve cvv cmpt2
      crn cuni cseqom cint wss crab cen wbr cmpt cdif cfn wcel weq fveq2 ineq1d
      ccom eqeq1d eqidd ifbieq12d ineq2 cbvmpt2v seqomeq12 mp2an sseq2d cbvrabv
      id fin23lem32 ) DEFGHUAIJMUBINZUANZOZJNZPZQRZVNVOSZUCZVLUDUEZUFZUDUGZKNZV
      LOZUHZKMUIZFMDNZWEPFNZUJUKDWEUIUEULZFMWFMWEUMZPWGUJUKDWIUIUEULZVTLAWEUNUO
      VLWJUSEWEENVLOWAUMULWHUSSZBCVRLHMUBLNZVLOZHNZPZQRZWNWOSZUCZRVSVSRVTWRVSUF
      RIJLHMUBVQWQWMVNPZQRZVNWSSILUPZVPWTVNVOVNWSXAVOWSQXAVMWMVNVKWLVLUQURZUTXA
      VNVAXBVBJHUPZWTWPVNWSWNWOXCWSWOQVNWNWMVCZUTXCVIXDVBVDVSTVRWRVSVSVEVFWDWAG
      NZVLOZUHKGMKGUPWCXFWAWBXEVLUQVGVHWHTWJTWKTVJ $.
      $( [2-Nov-2014] $)

    $d ph j a b c $.  $d A a b c j $.  $d B a b c j $.  $d Y a b c j $.
    fin23lem.f $e |- ( ph -> h : om -1-1-> _V ) $.
    fin23lem.g $e |- ( ph -> U. ran h C_ g ) $.
    fin23lem.h $e |- ( ph -> A. j ( ( j : om -1-1-> _V /\ U. ran j C_ g ) ->
        ( ( i ` j ) : om -1-1-> _V /\ U. ran ( i ` j ) C. U. ran j ) ) ) $.
    fin23lem.i $e |- Y = ( rec ( i , h ) |` om ) $.
    $( Lemma for ~ fin23 .  Establish induction invariants on ` Y ` which
       parameterizes our contradictory chain of subsets.  In this section,
       ` h ` is the hypothetically assumed family of subsets, ` g ` is the
       ground set, and ` i ` is the induction function constructed in the
       previous section. $)
    fin23lem34 $p |- ( ( ph /\ A e. om ) -> ( ( Y ` A ) : om -1-1-> _V /\
        U. ran ( Y ` A ) C_ g ) ) $=
      ( com cvv cfv wf1 crn cuni wss wa wceq va vb wcel cv wi c0 wb fveq2 f1eq1
      csuc syl rneqd unieqd sseq1d anbi12d imbi2d weq crdg cres fveq1i vex fr0g
      ax-mp eqtri rneqi unieqi anbi12i sylanbrc w3a wpss wal fvex rneq psseq12d
      sseq1i imbi12d cla4v imp pssss sylan expcom anim2d ad2antll 3adant1 frsuc
      sstr mpd fveq2i 3eqtr4g 3ad2ant1 mpbird 3exp a2d finds impcom ) BLUCALMBG
      NZOZWPPZQZCUDZRZSZALMUAUDZGNZOZXDPZQZWTRZSZUEALMUFGNZOZXJPZQZWTRZSZUEALMU
      BUDZGNZOZXQPZQZWTRZSZUEALMXPUJZGNZOZYDPZQZWTRZSZUEAXBUEUAUBBXCUFTZXIXOAYJ
      XEXKXHXNYJXDXJTXEXKUGXCUFGUHZLMXDXJUIUKYJXGXMWTYJXFXLYJXDXJYKULUMUNUOUPUA
      UBUQZXIYBAYLXEXRXHYAYLXDXQTXEXRUGXCXPGUHZLMXDXQUIUKYLXGXTWTYLXFXSYLXDXQYM
      ULUMUNUOUPXCYCTZXIYIAYNXEYEXHYHYNXDYDTXEYEUGXCYCGUHZLMXDYDUIUKYNXGYGWTYNX
      FYFYNXDYDYOULUMUNUOUPXCBTZXIXBAYPXEWQXHXAYPXDWPTXEWQUGXCBGUHZLMXDWPUIUKYP
      XGWSWTYPXFWRYPXDWPYQULUMUNUOUPALMDUDZOZYRPZQZWTRZXOHIXKYSXNUUBXJYRTXKYSUG
      XJUFEUDZYRURLUSZNZYRUFGUUDKUTYRMUCUUEYRTDVAYRMUUCVBVCVDZLMXJYRUIVCXMUUAWT
      XLYTXJYRUUFVEVFVOVGVHXPLUCZAYBYIUUGAYBYIUUGAYBVIYILMXQUUCNZOZUUHPZQZWTRZS
      ZAYBUUMUUGAYBSUUIUUKXTVJZSZUUMAYBUUOALMFUDZOZUUPPZQZWTRZSZLMUUPUUCNZOZUVB
      PZQZUUSVJZSZUEZFVKYBUUOUEZJUVHUVIFXQXPGVLUUPXQTZUVAYBUVGUUOUVJUUQXRUUTYAL
      MUUPXQUIUVJUUSXTWTUVJUURXSUUPXQVMUMZUNUOUVJUVCUUIUVFUUNUVJUVBUUHTUVCUUIUG
      UUPXQUUCUHZLMUVBUUHUIUKUVJUVEUUKUUSXTUVJUVDUUJUVJUVBUUHUVLULUMUVKVNUOVPVQ
      UKVRYAUUOUUMUEAXRYAUUNUULUUIUUNYAUULUUNUUKXTRYAUULUUKXTVSUUKXTWTWFVTWAWBW
      CWGWDUUGAYIUUMUGZYBUUGYDUUHTZUVMUUGYCUUDNXPUUDNZUUCNYDUUHYRXPUUCWEYCGUUDK
      UTXQUVOUUCXPGUUDKUTWHWIUVNYEUUIYHUULLMYDUUHUIUVNYGUUKWTUVNYFUUJYDUUHVMUMU
      NUOUKWJWKWLWMWNWO $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ fin23 .  Strict order property of ` Y ` . $)
    fin23lem35 $p |- ( ( ph /\ A e. om ) -> U. ran ( Y ` suc A ) C.
        U. ran ( Y ` A ) ) $=
      ( com wa cfv crn cuni wpss cv cvv wf1 wcel csuc wss fin23lem34 fvex f1eq1
      wi wal wceq rneq unieqd sseq1d anbi12d fveq2 rneqd psseq12d imbi12d cla4v
      wb syl adantr simprd crdg cres frsuc adantl fveq1i fveq2i 3eqtr4g psseq1d
      mpd mpbird ) ABLUAZMZBUBZGNZOZPZBGNZOZPZQVSERZNZOZPZWAQZVNLSWCTZWFVNLSVST
      ZWACRZUCZMZWGWFMZABCDEFGHIJKUDAWKWLUGZVMALSFRZTZWNOZPZWIUCZMZLSWNWBNZTZWT
      OZPZWQQZMZUGZFUHWMJXFWMFVSBGUEWNVSUIZWSWKXEWLXGWOWHWRWJLSWNVSUFXGWQWAWIXG
      WPVTWNVSUJUKZULUMXGXAWGXDWFXGWTWCUIXAWGUSWNVSWBUNZLSWTWCUFUTXGXCWEWQWAXGX
      BWDXGWTWCXIUOUKXHUPUMUQURUTVAVKVBVNVRWEWAVNVQWDVNVPWCVNVOWBDRZVCLVDZNZBXK
      NZWBNZVPWCVMXLXNUIAXJBWBVEVFVOGXKKVGVSXMWBBGXKKVGVHVIUOUKVJVL $.
      $( [2-Nov-2014] $)

    $( Lemma for ~ fin23 .  Weak order property of ` Y ` . $)
    fin23lem36 $p |- ( ( ( A e. om /\ B e. om ) /\ ( B C_ A /\ ph ) ) ->
        U. ran ( Y ` A ) C_ U. ran ( Y ` B ) ) $=
      ( wa wss cfv crn cuni wi fveq2 rneqd va vb com wcel cv csuc unieqd sseq1d
      wceq imbi2d weq ssid a1i12 wpss simprr simpll fin23lem35 syl2anc syl sstr
      pssss ex expr a2d findsg impr ) BUCUDCUCUDZMCBNABHOZPZQZCHOZPZQZNZAUAUEZH
      OZPZQZVMNZRAVMVMNZRAUBUEZHOZPZQZVMNZRAWAUFZHOZPZQZVMNZRAVNRUAUBBCVOCUIZVS
      VTAWKVRVMVMWKVQVLWKVPVKVOCHSTUGUHUJUAUBUKZVSWEAWLVRWDVMWLVQWCWLVPWBVOWAHS
      TUGUHUJVOWFUIZVSWJAWMVRWIVMWMVQWHWMVPWGVOWFHSTUGUHUJVOBUIZVSVNAWNVRVJVMWN
      VQVIWNVPVHVOBHSTUGUHUJVGAVTVMULUMWAUCUDZVGMZCWANZMAWEWJWPWQAWEWJRZWPWQAMZ
      MZWIWDNZWRWTWIWDUNZXAWTAWOXBWPWQAUOWOVGWSUPAWADEFGHIJKLUQURWIWDVAUSXAWEWJ
      WIWDVMUTVBUSVCVDVEVF $.
      $( [2-Nov-2014] $)

    $d Y a b c d $.  $d ph a b c d $.

    $( Lemma for ~ fin23 .  The contradictory chain has no minimum. $)
    fin23lem38 $p |- ( ph -> -. |^| { a | E. b e. om a =
          U. ran ( Y ` b ) } e. { a | E. b e. om a = U. ran ( Y ` b ) } ) $=
      ( vd vc cv cfv wceq com wrex wcel crn cuni cab cint cvv wa wpss wn peano2
      csuc eqid fveq2 rneqd unieqd eqeq2d rcla4ev mpan2 fvex rnex uniex rexbidv
      wss eqeq1 elab sylibr syl adantl intss1 fin23lem35 sspsstr syl2anc dfpss2
      simprbi nrexdv intnand weq cbvrexv syl6bb cbvabv elab4g sylnibr ) AGOZHOZ
      FPZUAZUBZQZHRSZGUCZUDZUETZWJMOZFPZUAZUBZQZMRSZUFWJWITAWQWKAWPMRAWLRTZUFZW
      JWOUGZWPUHZWSWJWLUJZFPZUAZUBZVBZXEWOUGWTWSXEWITZXFWRXGAWRXBRTZXGWLUIXHXEW
      FQZHRSZXGXHXEXEQZXJXEUKXIXKHXBRWCXBQZWFXEXEXLWEXDXLWDXCWCXBFULUMUNUOUPUQW
      HXJGXEXDXCXBFURUSUTWBXEQWGXIHRWBXEWFVCVAVDVEVFVGXEWIVHVFAWLBCDEFIJKLVIWJX
      EWOVJVKWTWJWOVBXAWJWOVLVMVFVNVONOZWOQZMRSZWQNWJWIXMWJQXNWPMRXMWJWOVCVAWHX
      OGNGNVPZWHXMWFQZHRSXOXPWGXQHRWBXMWFVCVAXQXNHMRHMVPZWFWOXMXRWEWNXRWDWMWCWL
      FULUMUNUOVQVRVSVTWA $.
      $( [2-Nov-2014] $)

    $d e Y $.  $d e ph $.
    $( Lemma for ~ fin23 .  Thus we have that ` g ` could not have been
       ` Fin3DS ` after all. $)
    fin23lem39 $p |- ( ph -> -. g e. Fin3DS ) $=
      ( vb vc ve cv wcel cfv crn com cvv wa vd cfin2ds cuni wceq cab fin23lem38
      wrex cint cmpt cpw wf csuc wss wral wf1 vex f1f dmfex sylancr mptexg 3syl
      wi fin23lem34 simprd elpw2 sylibr eqid fmptd wpss fin23lem35 pssss syl wb
      peano2 fveq2 rneqd unieqd fvex rnex uniex fvmpt weq sseq12d adantl mpbird
      ralrimiva jca32 wal df-fin2ds abeq2i fveq1 ralbidv anbi12d inteqd eleq12d
      feq1 rneq imbi12d cla4gv syl5bi com23 rnmpt inteqi eleq12i syl6ib mtod
      imp ) ABNZUBOZKNLNZFPZQZUCZUDLRUGKUEZUHZXNOZABCDEFKLGHIJUFAXILRXMUIZQZUHZ
      XROZXPAXQSOZRXHUJZXQUKZMNZULZXQPZYDXQPZUMZMRUNZTZTXIXTVBZAYAYCYIARSCNZUOZ
      RSOZYAGYMYLSORSYLUKYNCUPRSYLUQRSSYLURUSLRXMSUTVAALRXMYBXQAXJROTZXMXHUMZXM
      YBOYORSXKUOYPAXJBCDEFGHIJVCVDXMXHBUPVEVFXQVGZVHAYHMRAYDROZTZYHYEFPZQZUCZY
      DFPZQZUCZUMZYSUUBUUEVIUUFAYDBCDEFGHIJVJUUBUUEVKVLYRYHUUFVMAYRYFUUBYGUUEYR
      YEROYFUUBUDYDVNLYEXMUUBRXQXJYEUDZXLUUAUUGXKYTXJYEFVOVPVQYQUUAYTYEFVRVSVTW
      AVLLYDXMUUERXQLMWBZXLUUDUUHXKUUCXJYDFVOVPVQYQUUDUUCYDFVRVSVTWAWCWDWEWFWGY
      AYJYKYAXIYJXTXIRYBUANZUKZYEUUIPZYDUUIPZUMZMRUNZTZUUIQZUHZUUPOZVBZUAWHZYAY
      JXTVBZUUTBUBBUAMWIWJUUSUVAUAXQSUUIXQUDZUUOYJUURXTUVBUUJYCUUNYIRYBUUIXQWPU
      VBUUMYHMRUVBUUKYFUULYGYEUUIXQWKYDUUIXQWKWCWLWMUVBUUQXSUUPXRUVBUUPXRUUIXQW
      QZWNUVCWOWRWSWTXAXGVLXSXOXRXNXRXNLKRXMXQYQXBZXCUVDXDXEXF $.
      $( [4-Nov-2014] $)
  $}

  ${
    $d a b x $.
    $( Alternate definition of IV-finite sets: they lack a denumerable
       subset. $)
    dffin4-2 $p |- Fin4 = { x | -. om ~<_ x } $=
      ( va vb cfin4 com cv cdom wbr wn cab wpss cen wa wex wcel infpssr exlimiv
      vex infpssALT impbii notbii df-fin4 abeq2i weq breq2 notbid 3bitr4i eqriv
      elab ) BDEAFZGHZIZAJZCFZBFZKUNUOLHMZCNZIZEUOGHZIZUODOUOUMOUQUSUQUSUPUSCUO
      UNBRZPQCUOVASTUAURBDBCUBUCULUTAUOVAABUDUKUSUJUOEGUEUFUIUGUH $.
      $( [30-Oct-2014] $)
  $}


  ${
    $d a b c d e f g $.

    $( Lemma for ~ fin23 . ` Fin2 ` sets satisfy the descending chain
       condition. $)
    fin23lem40OLD $p |- ( g e. Fin2 -> A. a ( ( a : om --> ~P g /\
          A. b e. om ( a ` suc b ) C_ ( a ` b ) ) -> |^| ran a e. ran a ) ) $=
      ( vc cv cfin2 wcel com cpw cfv wss wral wa wi wne crpss wor adantr wceq
      c0 wf csuc crn cint dffin2-4 abeq2i frn vex rnex elpw sylibr cdm fdm ne0i
      peano1 ax-mp a1i eqnetrd dm0rn0 necon3bii sylib ccnv wfn wbr wpo ffn wpss
      wo sspss fvex brcnv brrpss bitri eqcom orbi12i sylbi ralimi adantl porpss
      biimpri cnvpo mpbi sornom syl3anc cnvso jca32 neeq1 soeq2 anbi12d eleq12d
      inteq id imbi12d rcla4cv imp3a syl5 alrimiv ) AEZFGZHWRIZBEZUAZCEZUBZXAJZ
      XCXAJZKZCHLZMZXAUCZUDZXJGZNZBWSDEZTOZXNPQZMZXNUDZXNGZNZDWTIZLZXMYBAFADUEU
      FXIXJYAGZXJTOZXJPQZMZMYBXLXIYCYDYEXBYCXHXBXJWTKYCHWTXAUGXJWTXABUHUIUJUKRX
      BYDXHXBXAULZTOYDXBYGHTHWTXAUMHTOZXBTHGYHUOHTUNUPUQURYGTXJTXAUSUTVARXIXJPV
      BZQZYEXIXAHVCZXFXEYIVDZXFXESZVHZCHLZXJYIVEZYJXBYKXHHWTXAVFRXHYOXBXGYNCHXG
      XEXFVGZXEXFSZVHZYNXEXFVIYNYSYLYQYMYRYLXEXFPVDYQXFXEPXCXAVJZXDXAVJVKXEXFYT
      VLVMXFXEVNVOVTVPVQVRYPXIXJPVEYPXJVSXJPWAWBUQYIXACWCWDXJPWEUKWFYBYCYFXLXTY
      FXLNDXJYAXNXJSZXQYFXSXLUUAXOYDXPYEXNXJTWGXNXJPWHWIUUAXRXKXNXJXNXJWKUUAWLW
      JWMWNWOWPVPWQ $.
      $( [3-Nov-2014] $)

    $( Lemma for ~ fin23 . ` Fin2 ` sets satisfy the descending chain
       condition. $)
    fin23lem40 $p |- Fin2 C_ Fin3DS $=
      ( vg va vb cfin2 cfin2ds cv wcel com cpw wf csuc cfv wss wral wa crn cint
      wi wal fin23lem40OLD df-fin2ds abeq2i sylibr ssriv ) ADEAFZDGHUEIBFZJCFZK
      UFLUGUFLMCHNOUFPZQUHGRBSZUEEGABCTUIAEABCUAUBUCUD $.
      $( [4-Nov-2014] $)

    $d a b c d e f g $.
    $( Lemma for ~ fin23 .  A set which satisfies the descending sequence
       condition must be III-finite. $)
    fin23lem41 $p |- Fin3DS C_ Fin3 $=
      ( va vb vd vc ve cfin2ds cfin3 cv wcel cfin4 com cdom wbr wn wf1 cvv cuni
      wa crn wss cpw wex vex pwex brdom cfv wpss wi fin23lem33 adantl crdg cres
      wal ssv f1ss mpan2 ad2antrr wf f1f frn uniss 3syl unipw syl6sseq weq rneq
      f1eq1 unieqd sseq1d anbi12d wceq wb fveq2 syl rneqd imbi12d cbvalv biimpi
      psseq12d eqid fin23lem39 ex exlimdv mpd pm2.01d exlimiv sylbi con2i breq2
      notbid dffin4-2 elab2 sylibr df-fin3 abeq2i ssriv ) AFGAHZFIZWQUAZJIZWQGI
      WRKWSLMZNZWTXAWRXAKWSBHZOZBUBWRNZKWSBWQAUCUDZUEXDXEBXDWRXDWRXEXDWRRZKPCHZ
      OZXHSZQZWQTZRZKPXHDHZUFZOZXOSZQZXKUGZRZUHZCUMZDUBZXEWRYCXDWQDCUIUJXGYBXED
      XGYBXEXGYBRABDEXNXCUKKULZXDKPXCOZWRYBXDWSPTYEWSUNKWSPXCUOUPUQXDXCSZQZWQTW
      RYBXDYGWSQZWQXDKWSXCURYFWSTYGYHTKWSXCUSKWSXCUTYFWSVAVBWQVCVDUQYBKPEHZOZYI
      SZQZWQTZRZKPYIXNUFZOZYOSZQZYLUGZRZUHZEUMZXGYBUUBYAUUACECEVEZXMYNXTYTUUCXI
      YJXLYMKPXHYIVGUUCXKYLWQUUCXJYKXHYIVFVHZVIVJUUCXPYPXSYSUUCXOYOVKXPYPVLXHYI
      XNVMZKPXOYOVGVNUUCXRYRXKYLUUCXQYQUUCXOYOUUEVOVHUUDVSVJVPVQVRUJYDVTWAWBWCW
      DWBWEWFWGWHKXCLMZNXBBWSJXFXCWSVKUUFXAXCWSKLWIWJBWKWLWMWTAGAWNWOWMWP $.
      $( [2-Nov-2014] $)
  $}

  ${
    $( The union (supremum) of a finite set of finite ordinals is a finite
       ordinal. $)
    nnunifi $p |- ( ( S C_ om /\ S e. Fin ) -> U. S e. om ) $=
      ( com wss cfn wcel wa cuni wceq unieq uni0 peano1 eqeltri syl6eqel adantl
      c0 wne simpll con0 omsson syl6ss simplr simpr ordunifi syl3anc pm2.61dane
      sseldd ) ABCZADEZFZAGZBEZAOAOHZUKUIULUJOGZBAOIUMOBJKLMNUIAOPZFZABUJUGUHUN
      QZUOARCUHUNUJAEUOABRUPSTUGUHUNUAUIUNUBAUCUDUFUE $.
      $( [5-Nov-2014] $)
  $}

  ${
    df32lem.a $e |- ( ph -> f : om --> ~P g ) $.
    df32lem.b $e |- ( ph -> A. x e. om ( f ` suc x ) C_ ( f ` x ) ) $.
    df32lem.c $e |- ( ph -> -. |^| ran f e. ran f ) $.
    $d ph a b c d e s t u v w x y $.  $d A a b c d e s t u v w x y $.
    $d B a b c d e s t u v w x y $.  $d a b c d e s t u v w x y f g $.

    $( Lemma for ~ dffin3-2 .  Derive weak ordering property. $)
    df32lem1 $p |- ( ( ( A e. om /\ B e. om ) /\ ( B C_ A /\ ph ) ) ->
        ( f ` A ) C_ ( f ` B ) ) $=
      ( va vb com wcel wss cv cfv wi fveq2 sseq1d imbi2d wa csuc wceq weq a1i12
      ssid wral suceq fveq2d sseq12d rcla4v syl5 ad2antrr sstr2 syl6 a2d findsg
      impr ) CLMDLMZUADCNACEOZPZDUTPZNZAJOZUTPZVBNZQAVBVBNZQAKOZUTPZVBNZQAVHUBZ
      UTPZVBNZQAVCQJKCDVDDUCZVFVGAVNVEVBVBVDDUTRSTJKUDZVFVJAVOVEVIVBVDVHUTRSTVD
      VKUCZVFVMAVPVEVLVBVDVKUTRSTVDCUCZVFVCAVQVEVAVBVDCUTRSTUSAVGVBUFUEVHLMZUSU
      ADVHNZUAZAVJVMVTAVLVINZVJVMQVRAWAQUSVSABOZUBZUTPZWBUTPZNZBLUGVRWAHWFWABVH
      LBKUDZWDVLWEVIWGWCVKUTWBVHUHUIWBVHUTRUJUKULUMVLVIVBUNUOUPUQUR $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ dffin3-2 .  Non-minimum implies that there is always another
       decrease. $)
    df32lem2 $p |- ( ( ph /\ A e. om ) -> E. a e. om ( A e. a /\
        ( f ` suc a ) C. ( f ` a ) ) ) $=
      ( vb com wcel wa cv cfv wceq wi wss syl fveq2 vc vd csuc wn wrex wpss crn
      wral cint adantr wfn cpw wf ffn peano2 fnfvelrn syl2an intss1 wb ad2antrr
      fvelrnb wo word nnord ad2antlr ordtri2or2 syl2anc simplrr simpllr simplrl
      ad2antll simpr eqeq2d imbi2d weq eqid1 a1i12 sucexb sylibr adantl sucssel
      cvv elex imp eleq2 suceq fveq2d eqeq12d imbi12d rcla4v com23 eqtr3 expcom
      mpd syl6 a2d findsg syl22anc eqimss simplll df32lem1 jaodan mpdan anassrs
      impr sseq2 syl5ibcom rexlimdva sylbid ralrimiv ssint eqssd eqeltrd rexnal
      mtand sseq12d cbvralv sylib pm4.61 dfpss2 anim2d syl5bi ralimi rexim 3syl
      simplbi2 ) ACKLZMZCFNZLZYIUCZDNZOZYIYLOZPZQZUDZFKUEZYJYMYNUFZMZFKUEZYHYPF
      KUHZUDYRYHUUBYLUGZUIZUUCLZAUUEUDYGIUJYHUUBMZUUDCUCZYLOZUUCUUFUUDUUHUUFUUH
      UUCLZUUDUUHRYHUUIUUBAYLKUKZUUGKLZUUIYGAKENULZYLUMUUJGKUULYLUNSZCUOZKUUGYL
      UPUQUJZUUHUUCURSUUFUUHJNZRZJUUCUHUUHUUDRUUFUUQJUUCUUFUUPUUCLZUANZYLOZUUPP
      ZUAKUEZUUQAUURUVBUSZYGUUBAUUJUVCUUMUAKUUPYLVASUTUUFUVAUUQUAKUUFUUSKLZMUUH
      UUTRZUVAUUQYHUUBUVDUVEYHUUBUVDMZMZUUGUUSRZUUSUUGRZVBZUVEUVGUUGVCZUUSVCZUV
      JYGUVKAUVFYGUUKUVKUUNUUGVDSVEUVDUVLYHUUBUUSVDVKUUGUUSVFVGUVGUVHUVEUVIUVGU
      VHMZUUHUUTPZUVEUVMUVDUUKUVHUUBUVNYHUUBUVDUVHVHUVMYGUUKAYGUVFUVHVIUUNSUVGU
      VHVLYHUUBUVDUVHVJUVDUUKMUVHUUBUVNUUBUUHUUPYLOZPZQUUBUUHUUHPZQUUBUUHUBNZYL
      OZPZQUUBUUHUVRUCZYLOZPZQUUBUVNQJUBUUSUUGUUPUUGPZUVPUVQUUBUWDUVOUUHUUHUUPU
      UGYLTVMVNJUBVOZUVPUVTUUBUWEUVOUVSUUHUUPUVRYLTVMVNUUPUWAPZUVPUWCUUBUWFUVOU
      WBUUHUUPUWAYLTVMVNJUAVOZUVPUVNUUBUWGUVOUUTUUHUUPUUSYLTVMVNUUKUUBUVQUUHVPV
      QUVRKLZUUKMZUUGUVRRZMZUUBUVTUWCUWKUUBUWBUVSPZUVTUWCQUWKCUVRLZUUBUWLQZUWIU
      WJUWMUWICWBLZUWJUWMQUUKUWOUWHUUKUUGWBLUWOUUGKWCCVRVSVTCUVRWBWASWDUWHUWMUW
      NQUUKUWJUWHUUBUWMUWLYPUWMUWLQFUVRKFUBVOZYJUWMYOUWLYIUVRCWEUWPYMUWBYNUVSUW
      PYKUWAYLYIUVRWFWGYIUVRYLTWHWIWJWKUTWNUVTUWLUWCUUHUWBUVSWLWMWOWPWQXEWRUUHU
      UTWSSUVGUVIMZUUKUVDUVIAUVEUWQYGUUKAYGUVFUVIVIUUNSYHUUBUVDUVIVHUVGUVIVLAYG
      UVFUVIWTABUUGUUSDEGHIXAWRXBXCXDUUTUUPUUHXFXGXHXIXJJUUHUUCXKVSXLUUOXMXOYPF
      KXNVSYHYMYNRZFKUHZYQYTQZFKUHYRUUAQAUWSYGABNZUCZYLOZUXAYLOZRZBKUHUWSHUXEUW
      RBFKBFVOZUXCYMUXDYNUXFUXBYKYLUXAYIWFWGUXAYIYLTXPXQXRUJUWRUWTFKYQYJYOUDZMU
      WRYTYJYOXSUWRUXGYSYJYSUWRUXGYMYNXTYFYAYBYCYQYTFKYDYEWN $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ dffin3-2 .  Being a chain, difference sets are disjoint (one
       case). $)
    df32lem3 $p |- ( ( ( A e. om /\ B e. om ) /\ ( B e. A /\ ph ) ) ->
        ( ( ( f ` A ) \ ( f ` suc A ) ) i^i
          ( ( f ` B ) \ ( f ` suc B ) ) ) = (/) ) $=
      ( va com wcel wa cv cfv csuc cdif wn wral wss cin c0 eldifi simpll peano2
      wceq ad2antlr word ad2antrr simprl ordsucss sylc simprr df32lem1 syl22anc
      nnord sseld elndif syl6 syl5 ralrimiv disj sylibr ) CKLZDKLZMZDCLZAMZMZJN
      ZDENZOZDPZVKOZQZLRZJCVKOZCPVKOZQZSVSVOUAUBUFVIVPJVSVJVSLVJVQLZVIVPVJVQVRU
      CVIVTVJVNLVPVIVQVNVJVIVDVMKLZVMCTZAVQVNTVDVEVHUDVEWAVDVHDUEUGVICUHZVGWBVD
      WCVEVHCUPUIVFVGAUJDCUKULVFVGAUMABCVMEFGHIUNUOUQVJVNVLURUSUTVAJVSVOVBVC $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ dffin3-2 .  Being a chain, difference sets are disjoint. $)
    df32lem4 $p |- ( ( ( ph /\ A =/= B ) /\ ( A e. om /\ B e. om ) ) ->
        ( ( ( f ` A ) \ ( f ` suc A ) ) i^i
          ( ( f ` B ) \ ( f ` suc B ) ) ) = (/) ) $=
      ( wa com wcel cfv csuc cdif cin c0 wceq word nnord wne wo cv simplr wn wb
      ordtri3 syl2an adantl mpbird simplrr simplrl simpr simplll incom df32lem3
      necon2abid syl5eq syl22anc jaodan mpdan ) ACDUAZJZCKLZDKLZJZJZCDLZDCLZUBZ
      CEUCZMCNVKMOZDVKMDNVKMOZPZQRZVGVJVBAVBVFUDVGVJCDVFCDRVJUEUFZVCVDCSDSVPVEC
      TDTCDUGUHUIUQUJVGVHVOVIVGVHJVEVDVHAVOVCVDVEVHUKVCVDVEVHULVGVHUMAVBVFVHUNV
      EVDJVHAJJVNVMVLPQVLVMUOABDCEFGHIUPURUSVGVIJVDVEVIAVOVCVDVEVIULVCVDVEVIUKV
      GVIUMAVBVFVIUNABCDEFGHIUPUSUTVA $.
      $( [5-Nov-2014] $)

    $d S a b c d g s t u v w x y $.
    df32lem.d $e |- S = { y e. om | ( f ` suc y ) C. ( f ` y ) } $.
    $( Lemma for ~ dffin3-2 .  There are infinite decrease points. $)
    df32lem5 $p |- ( ph -> -. S e. Fin ) $=
      ( va vb wcel cv cfv wa com wrex wn con0 csuc wpss wral df32lem2 ralrimiva
      cfn wel cuni crab ssrab2 eqsstri nnunifi mpan adantl wi elssuni wb omsson
      wss nnon sseldi ontri1 syl2anr syl5ib con2d impr eleq2i sylnib weq fveq2d
      suceq fveq2 psseq12d elrab3 ad2antrl mtbid expr imnan sylib nrexdv anbi1d
      wceq eleq1 rexbidv notbid rcla4ev syl2anc rexnal ex mt2d ) ADUFMZKLUGZLNZ
      UAZENZOZWMWOOZUBZPZLQRZKQUCZAWTKQABKNZEFLGHIUDUEAWKXASZAWKPZWTSZKQRZXCXDD
      UHZQMZXGWMMZWRPZLQRZSZXFWKXHADQUSWKXHDCNZUAZWOOZXMWOOZUBZCQUIZQJXQCQUJUKD
      ULUMUNZXDXJLQXDWMQMZPZXIWRSZUOXJSXDXTXIYBXDXTXIPPZWMXRMZWRYCWMDMZYDXDXTXI
      YESYAYEXIYEWMXGUSZYAXISZWMDUPXTWMTMXGTMYFYGUQXDWMUTXDQTXGURXSVAWMXGVBVCVD
      VEVFDXRWMJVGVHXTYDWRUQXDXIXQWRCWMQCLVIZXOWPXPWQYHXNWNWOXMWMVKVJXMWMWOVLVM
      VNVOVPVQXIWRVRVSVTXEXLKXGQXBXGWBZWTXKYIWSXJLQYIWLXIWRXBXGWMWCWAWDWEWFWGWT
      KQWHVSWIWJ $.
      $( [5-Nov-2014] $)

    $d J a b c d s t w x y $.  $d K a b c d s t x y $.
    df32lem.e $e |- J = ( u e. om |-> U. { v e. S | ( v i^i S ) ~~ u } ) $.
    df32lem.f $e |- K = ( ( w e. S |-> ( ( f ` w ) \ ( f ` suc w ) ) ) o.
      J ) $.
    $( Lemma for ~ dffin3-2 .  Each K value is non-empty. $)
    df32lem6 $p |- ( ( ph /\ A e. om ) -> ( K ` A ) =/= (/) ) $=
      ( com cfv wcel wa cv csuc cdif cmpt ccom fveq1i wfun wceq funmpt a1i wf1o
      c0 wf wss cfn wpss crab ssrab2 eqsstri df32lem5 adantr fin23lem22 sylancr
      f1of syl simpr fvco3 syl3anc ffvelrn sylancom fveq2 suceq fveq2d difeq12d
      eqid cvv fvex difexg ax-mp fvmpt eqtrd syl5eq wne psseq12d elrab2 simprbi
      wn df-pss biimpi pssdifn0 3syl eqnetrd ) AGSUAZUBZGLTZGKTZIUCZTZWRUDZWSTZ
      UEZUNWPWQGDHDUCZWSTZXDUDZWSTZUEZUFZKUGZTZXCGLXJRUHWPXKWRXITZXCWPXIUIZSHKU
      OZWOXKXLUJXMWPDHXHUKULWPSHKUMZXNWPHSUPHUQUAWIZXOHCUCZUDZWSTZXQWSTZURZCSUS
      SPYACSUTVAAXPWOABCHIJMNOPVBVCKHFEQVDVESHKVFVGZAWOVHSHGXIKVIVJWPWRHUAZXLXC
      UJAWOXNYCYBSHGKVKVLZDWRXHXCHXIXDWRUJZXEWTXGXBXDWRWSVMYEXFXAWSXDWRVNVOVPXI
      VQWTVRUAXCVRUAWRWSVSWTXBVRVTWAWBVGWCWDWPXBWTURZXBWTUPXBWTWEUBZXCUNWEWPYCY
      FYDYCWRSUAYFYAYFCWRSHXQWRUJZXSXBXTWTYHXRXAWSXQWRVNVOXQWRWSVMWFPWGWHVGYFYG
      XBWTWJWKXBWTWLWMWN $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ dffin3-2 .  Different K values are disjoint. $)
    df32lem7 $p |- ( ( ( ph /\ A =/= B ) /\ ( A e. om /\ B e. om ) ) ->
        ( ( K ` A ) i^i ( K ` B ) ) = (/) ) $=
      ( com wne wa wcel cfv cin cv csuc cdif c0 cmpt ccom fveq1i wfun wf funmpt
      wceq a1i wf1o wss wn wpss crab ssrab2 eqsstri df32lem5 fin23lem22 sylancr
      cfn f1of syl simprl fvco3 syl3anc adantr simpl ffvelrn syl2an fveq2 suceq
      ad2antrr fveq2d difeq12d eqid fvex difexg ax-mp fvmpt eqtrd syl5eq simprr
      cvv simpr ineq12d simpll simplr wf1 f1of1 f1fveq sylan biimpd necon3d mpd
      wb sseldi df32lem4 syl22anc ) AGHUAZUBZGTUCZHTUCZUBZUBZGMUDZHMUDZUEGLUDZJ
      UFZUDZXOUGZXPUDZUHZHLUDZXPUDZYAUGZXPUDZUHZUEZUIXLXMXTXNYEXLXMGDIDUFZXPUDZ
      YGUGZXPUDZUHZUJZLUKZUDZXTGMYMSULXLYNXOYLUDZXTXLYLUMZTILUNZXIYNYOUPYPXLDIY
      KUOUQZAYQXGXKATILURZYQAITUSIVHUCUTYSICUFZUGXPUDYTXPUDVAZCTVBTQUUACTVCVDZA
      BCIJKNOPQVELIFERVFVGZTILVIVJZVTZXHXIXJVKTIGYLLVLVMXLXOIUCZYOXTUPXHYQXIUUF
      XKAYQXGUUDVNZXIXJVOTIGLVPVQZDXOYKXTIYLYGXOUPZYHXQYJXSYGXOXPVRUUIYIXRXPYGX
      OVSWAWBYLWCZXQWKUCXTWKUCXOXPWDXQXSWKWEWFWGVJWHWIXLXNHYMUDZYEHMYMSULXLUUKY
      AYLUDZYEXLYPYQXJUUKUULUPYRUUEXHXIXJWJTIHYLLVLVMXLYAIUCZUULYEUPXHYQXJUUMXK
      UUGXIXJWLTIHLVPVQZDYAYKYEIYLYGYAUPZYHYBYJYDYGYAXPVRUUOYIYCXPYGYAVSWAWBUUJ
      YBWKUCYEWKUCYAXPWDYBYDWKWEWFWGVJWHWIWMXLAXOYAUAZXOTUCYATUCYFUIUPAXGXKWNXL
      XGUUPAXGXKWOXLXOYAGHXLXOYAUPZGHUPZXHTILWPZXKUUQUURXCAUUSXGAYSUUSUUCTILWQV
      JVNTIGHLWRWSWTXAXBXLITXOUUBUUHXDXLITYAUUBUUNXDABXOYAJKNOPXEXFWH $.
      $( [5-Nov-2014] $)

    $( Lemma for ~ dffin3-2 .  K sets are subsets of the base. $)
    df32lem8 $p |- ( ( ph /\ A e. om ) -> ( K ` A ) C_ g ) $=
      ( com cfv wcel wa cv csuc cdif cmpt ccom fveq1i wfun wceq funmpt a1i wf1o
      wf wss cfn wn wpss crab ssrab2 eqsstri df32lem5 fin23lem22 sylancr adantr
      f1of syl simpr fvco3 syl3anc ffvelrn sylan fveq2 fveq2d difeq12d eqid cvv
      suceq fvex difexg ax-mp fvmpt eqtrd syl5eq difss cpw sseldi syl2anc elpw2
      vex sylib syl5ss eqsstrd ) AGSUAZUBZGLTZGKTZIUCZTZWQUDZWRTZUEZJUCZWOWPGDH
      DUCZWRTZXDUDZWRTZUEZUFZKUGZTZXBGLXJRUHWOXKWQXITZXBWOXIUIZSHKUNZWNXKXLUJXM
      WODHXHUKULAXNWNASHKUMZXNAHSUOHUPUAUQXOHCUCZUDWRTXPWRTURZCSUSSPXQCSUTVAZAB
      CHIJMNOPVBKHFEQVCVDSHKVFVGZVEAWNVHSHGXIKVIVJWOWQHUAZXLXBUJAXNWNXTXSSHGKVK
      VLZDWQXHXBHXIXDWQUJZXEWSXGXAXDWQWRVMYBXFWTWRXDWQVRVNVOXIVPWSVQUAXBVQUAWQW
      RVSWSXAVQVTWAWBVGWCWDWOXBWSXCWSXAWEWOWSXCWFZUAZWSXCUOWOSYCWRUNZWQSUAYDAYE
      WNMVEWOHSWQXRYAWGSYCWQWRVKWHWSXCJWJWIWKWLWM $.
      $( [6-Nov-2014] $)

    $d L a b c d x $.
    df32lem.g $e |- L = ( t e. g |-> if ( E! s e. om t e. ( K ` s ) ,
        ( iota_ s e. om t e. ( K ` s ) ) , (/) ) ) $.
    $( Lemma for ~ dffin3-2 .  Construction of the onto function. $)
    df32lem9 $p |- ( ph -> L : g -onto-> om ) $=
      ( va vb cv com wf cfv wceq wrex wral wfo wcel wreu crio c0 cif wel adantl
      riotacl wn wa peano1 a1i ifclda rgen fmpt wex wne df32lem6 sylib df32lem8
      mpbi sselda weq eleq1 reubidv riotabidv eqidd ifbieq12d riotaex 0ex fvmpt
      n0 ifex syl w3a simp1r wal cin simpl1 simpr necomd simpl2 simpl3 df32lem7
      wi syl22anc disj1 ax-4 syl6 com23 3adant1r mpd necon4ad eleq2d syl5ibrcom
      ex fveq2 impbid riota5 an32s simplr eqeltrd cvv wb cpw vex dmfex ad2antrr
      sylancr riotaclbg mpbird iftrue 3eqtrrd jca eximdv df-rex ralrimiva dffo3
      syl6ibr sylanbrc ) AJUDZUEMUFZUBUDZUCUDZMUGZUHZUCYLUIZUBUEUJYLUEMUKYMAGUD
      ZNUDZLUGZULZNUEUMZUUBNUEUNZUOUPZUEULZGYLUJYMUUFGYLGJUQZUUCUUDUOUEUUCUUDUE
      ULUUGUUBNUEUSURUOUEULUUGUUCUTVAVBVCVDVEGYLUEUUEMUAVFVLVCAYRUBUEAYNUEULZVA
      ZYOYNLUGZULZUCVGZYRUUIUUJUOVHUULABCDEFYNHIJKLOPQRSTVIUCUUJWCVJUUIUULUCJUQ
      ZYQVAZUCVGYRUUIUUKUUNUCUUIUUKUUNUUIUUKVAZUUMYQUUIUUJYLYOABCDEFYNHIJKLOPQR
      STVKVMZUUOYPYOUUAULZNUEUMZUUQNUEUNZUOUPZUUSYNUUOUUMYPUUTUHUUPGYOUUEUUTYLM
      GUCVNZUUCUURUUDUOUUSUOUVAUUBUUQNUEYSYOUUAVOZVPUVAUUBUUQNUEUVBVQUVAUOVRVSU
      AUURUUSUOUUQNUEVTWAWDWBWEUUOUURUUTUUSUHUUOUURUUSUEULZUUOUUSYNUEAUUKUUHUUS
      YNUHAUUKVAZUUQNUEYNUVDUUHYTUEULZWFZUUQNUBVNZUVFUUQYTYNUVFUUKYTYNVHZUUQUTZ
      WPZAUUKUUHUVEWGZAUUHUVEUUKUVJWPUUKAUUHUVEWFZUVHUUKUVIUVLUVHUUKUVIWPZUCWHZ
      UVMUVLUVHUVNUVLUVHVAZUUJUUAWIUOUHZUVNUVOAYNYTVHUUHUVEUVPAUUHUVEUVHWJUVOYT
      YNUVLUVHWKWLAUUHUVEUVHWMAUUHUVEUVHWNABCDEFYNYTHIJKLOPQRSTWOWQUCUUJUUAWRVJ
      XGUVMUCWSWTXAXBXCXDUVFUUQUVGUUKUVKUVGUUAUUJYOYTYNLXHXEXFXIXJXKZAUUHUUKXLX
      MUUOUEXNULZUURUVCXOAUVRUUHUUKAIUDZXNULUEYLXPZUVSUFUVRIXQOUEUVTXNUVSXRXTXS
      UUQNUEXNYAWEYBUURUUSUOYCWEUVQYDYEXGYFYQUCYLYGYJXCYHUCUBYLUEMYIYK $.
      $( [5-Nov-2014] $)

    $( Lemma for dffin3-2 .  Wrap in existential. $)
    df32lem10 $p |- ( ph -> E. a a : g -onto-> om ) $=
      ( cv com wfo wex df32lem9 cvv wcel wf fof vex fex mpan2 syl foeq1 cla4egv
      id sylc ) AJUCZUDMUEZUTUDOUCZUEZOUFZABCDEFGHIJKLMNPQRSTUAUBUGVAMUHUIZVAVD
      VAUTUDMUJZVEUTUDMUKVFUTUHUIVEJULUTUDUHMUMUNUOVAURVCVAOMUHUTUDVBMUPUQUSUO
      $.
      $( [6-Nov-2014] $)
  $}

  ${
    $d A x y a b $.  $d F a b y $.  $d G a b x y $.
    compssiso.a $e |- F = ( x e. ~P A |-> ( A \ x ) ) $.
    compssiso.b $e |- A e. _V $.
    $( Complementation is an antiautomorphism on power set latticies. $)
    compssiso $p |- F Isom {C.} , `' {C.} ( ~P A , ~P A ) $=
      ( va vb crpss wbr wb cvv wcel cdif wa wss elpw2 wceq bitri difeq2 sscon
      cpw ccnv wiso wf1o cv cfv wral df-iso difss mpbir a1i dfss4 biimpi eqcomd
      wi eqeq2d syl5ibrcom adantl adantr impbid f1o2d ax-mp wpss sseq12 syl2anr
      wn syl5ib impbid2 ancoms notbid anbi12d dfpss3 3bitr4g brrpss brcnv fvmpt
      vex difexg breqan12d bitr4d rgen2a mpbir2an ) BUAZWCHHUBZCUCWCWCCUDZFUEZG
      UEZHIZWFCUFZWGCUFZWDIZJZGWCUGFWCUGFGWCWCHWDCUHBKLZWEEWMAFWCWCBAUEZMZBWFMZ
      CDWOWCLZWMWNWCLZNWQWOBOBWNUIWOBEPUJUKWPWCLZWMWFWCLZNWSWPBOBWFUIWPBEPUJUKW
      RWTNZWNWPQZWFWOQZJWMXAXBXCWTXBXCUOWRWTXCXBWFBWPMZQWTXDWFWTXDWFQZWTWFBOXEW
      FBEPWFBULRUMZUNXBWOXDWFWNWPBSUPUQURWRXCXBUOWTWRXBXCWNBWOMZQWRXGWNWRXGWNQZ
      WRWNBOXHWNBEPWNBULRUMUNXCWPXGWNWFWOBSUPUQUSUTURVAVBWLFGWCWTWGWCLZNZWHWPBW
      GMZWDIZWKXJWFWGVCZXKWPVCZWHXLXJWFWGOZWGWFOZVFZNXKWPOZWPXKOZVFZNXMXNXJXOXR
      XQXTXIWTXOXRJXIWTNZXOXRWFWGBTXRXDBXKMZOZYAXOXKWPBTWTXEYBWGQZYCXOJXIXFXIYD
      XIWGBOYDWGBEPWGBULRUMZXDWFYBWGVDVEVGVHVIXJXPXSXJXPXSWGWFBTXSYBXDOZXJXPWPX
      KBTXIYDXEYFXPJWTYEXFYBWGXDWFVDVEVGVHVJVKWFWGVLXKWPVLVMWFWGGVQVNXLXKWPHIXN
      WPXKHWMWPKLEBWFKVRVBZWMXKKLEBWGKVRVBZVOXKWPYGVNRVMWTXIWIWPWJXKWDAWFWOWPWC
      CWNWFBSDYGVPAWGWOXKWCCWNWGBSDYHVPVSVTWAWB $.
    $( [4-Nov-2014] $)

    $( Express image under of the complementation isomorphism. $)
    compss $p |- ( G C_ ~P A -> ( F " G ) = { y e. ~P A | ( A \ y ) e. G } ) $=
      ( va vb wss cv cdif wcel wceq wrex wa wb difeq2 cvv elpw2 cima crab ssel2
      cpw cfv difexg ax-mp fvmpt syl rexbidva difss mpbir eleq1 mpbii rexlimivw
      eqeq1d pm4.71ri dfss4 biimpi adantlr eqcomd syl5ibcom ad2antlr syl5ibrcom
      bitri eqeq2d impbid risset syl6bbr pm5.32da syl5bb bitrd wfn a1i fvelimab
      fnmpt mprg mpan weq eleq1d elrab 3bitr4d eqrdv ) ECUDZJZHDEUAZCBKZLZEMZBW
      DUBZWEIKZDUEZHKZNZIEOZWMWDMZCWMLZEMZPZWMWFMZWMWJMZWEWOCWKLZWMNZIEOZWSWEWN
      XCIEWEWKEMZPZWKWDMZWNXCQEWDWKUCZXGWLXBWMAWKCAKZLZXBWDDXIWKCRFCSMZXBSMGCWK
      SUFUGUHUPUIUJXDWPXDPWEWSXDWPXCWPIEXCXBWDMZWPXLXBCJCWKUKXBCGTULXBWMWDUMUNU
      OUQWEWPXDWRWEWPPZXDWKWQNZIEOWRXMXCXNIEXMXEPZXCXNXOWKCXBLZNXCXNXOXPWKWEXEX
      PWKNZWPXFXGXQXHXGXQXGWKCJXQWKCGTWKCURVEUSUIUTVAXCXPWQWKXBWMCRVFVBXOXCXNCW
      QLZWMNZWPXSWEXEWPXSWPWMCJXSWMCGTWMCURVEUSVCXNXBXRWMWKWQCRUPVDVGUJIWQEVHVI
      VJVKVLDWDVMZWEWTWOQXJSMZXTAWDAWDXJDSFVPYAXIWDMXKYAGCXISUFUGVNVQIWDEWMDVOV
      RXAWSQWEWIWRBWMWDBHVSWHWQEWGWMCRVTWAVNWBWC $.
      $( [5-Nov-2014] $)
  $}

  ${
    $d A a b c $.  $d B a b c $.  $d F a b c $.

    $( Lemma for ~ dffin3-2 .  Covering implies injection on power sets. $)
    df32lem11 $p |- ( ( F e. _V /\ F : A -onto-> B ) -> ~P B ~<_ ~P A ) $=
      ( va vb cvv wcel wa cpw syl cv cima wss wceq adantl imaeq2 vex elpw sylib
      wb wfo cdom wbr fof dmfex sylan2 pwexg ccnv crn imassrn cdm dfdm4 syl5eqr
      wf fdm syl5sseq cnvexg adantr imaexg elpwg mpbird a1d weq simpllr simplrl
      3syl foimacnv syl2anc simplrr 3eqtr3d ex impbid1 dom3d mpd ) CFGZABCUAZHZ
      AIZFGZBIZVRUBUCVQAFGZVSVPVOABCUNZWAABCUDZABFCUEUFAFUGJVQDEVTVRCUHZDKZLZWD
      EKZLZFVQWFVRGZWEVTGZVQWIWFAMZVPWKVOVPWDUIZWFAWDWEUJVPWLCUKZACULVPWBWMANWC
      ABCUOJUMUPOVQWDFGZWFFGWIWKTVOWNVPCFUQURWDWEFUSWFAFUTVFVAVBVQWJWGVTGZHZWFW
      HNZDEVCZTVQWPHZWQWRWSWQWRWSWQHZCWFLZCWHLZWEWGWQXAXBNWSWFWHCPOWTVPWEBMZXAW
      ENVOVPWPWQVDZWTWJXCVQWJWOWQVEWEBDQRSABWECVGVHWTVPWGBMZXBWGNXDWTWOXEVQWJWO
      WQVIWGBEQRSABWGCVGVHVJVKWEWGWDPVLVKVMVN $.
      $( [6-Nov-2014] $)

    $d a b c d e f g h i j k l x y $.

    $( Lemma for ~ dffin3-2 .  Remove hypotheses from ~ df32lem9 . $)
    df32lem12 $p |- ( -. j e. Fin3DS -> E. i i : j -onto-> om ) $=
      ( va vb vc vd vh vg vf vk ve vl cv wcel wn com csuc cfv cmpt eqid cfin2ds
      cpw wf wss wral wa crn wi wal wfo wex df-fin2ds abeq2i notbii exnal annim
      cint wpss crab cin cen wbr cuni cdif ccom wreu crio cif simpll weq fveq2d
      c0 suceq fveq2 sseq12d cbvralv biimpi ad2antlr psseq12d cbvrabv df32lem10
      simpr sylbir exlimiv sylbi ) BMZUANZOPWFUBCMZUCZDMZQZWHRZWJWHRZUDZDPUEZUF
      ZWHUGZUQWQNZUHZCUIZOZWFPAMUJAUKZWGWTWTBUABCDULUMUNXAWSOZCUKXBWSCUOXCXBCXC
      WPWROZUFZXBWPWRUPXEEFGHIJKMZQZWHRZXFWHRZURZKPUSZCBIPHMXKUTIMVAVBHXKUSVCSZ
      GXKGMZWHRXMQWHRVDSXLVEZJWFJMLMXNRNZLPVFXOLPVGVLVHSZLAWIWOXDVIWOEMZQZWHRZX
      QWHRZUDZEPUEZWIXDWOYBWNYADEPDEVJZWLXSWMXTYCWKXRWHWJXQVMVKWJXQWHVNVOVPVQVR
      WPXDWBXJFMZQZWHRZYDWHRZURKFPKFVJZXHYFXIYGYHXGYEWHXFYDVMVKXFYDWHVNVSVTXLTX
      NTXPTWAWCWDWCWE $.
      $( [6-Nov-2014] $)

    $( Weakly Dedekind-infinite sets are exactly those which can be mapped onto
       ` om ` . $)
    dffin3-2 $p |- Fin3 = { x | -. E. y y : x -onto-> om } $=
      ( va vb cfin3 cv com wfo wex cab wcel cpw cdom wbr cvv vex notbid cfin2ds
      wn cfin4 csdm wi fornex ax-mp canth2g sdomdom 3syl df32lem11 mpan syl2anc
      domtr df-fin3 abeq2i pwex wceq breq2 dffin4-2 elab2 bitri con2bii exlimiv
      sylib con2i fin23lem41 df32lem12 con1i sseldi impbii weq foeq2 elab eqriv
      exbidv bitr4i ) CEAFZGBFZHZBIZSZAJZCFZEKZWAGVPHZBIZSZWAVTKWBWEWDWBWCWBSZB
      WCGWALZMNZWFWCGGLZMNZWIWGMNZWHWCGOKZGWIUANWJWAOKWCWLUBCPZWAGOVPUCUDGOUEGW
      IUFUGVPOKWCWKBPWAGVPUHUIGWIWGUKUJWBWHWBWGTKZWHSZWNCECULUMGDFZMNZSWODWGTWA
      WMUNWPWGUOWQWHWPWGGMUPQDUQURUSUTVBVAVCWEREWAVDWARKWDBCVEVFVGVHVSWEAWAWMAC
      VIZVRWDWRVQWCBVOWAGVPVJVMQVKVNVL $.
      $( [6-Nov-2014] $)

    $( Weakly Dedekind-infinite sets are exactly those with an ` om ` -indexed
       descending chain of subsets. $)
    dffin3-3 $p |- Fin3 = { g | A. a ( ( a : om --> ~P g /\
        A. b e. om ( a ` suc b ) C_ ( a ` b ) ) -> |^| ran a e. ran a ) } $=
      ( cfin3 cfin2ds com cv cpw wf csuc cfv wss wral wa crn cint wcel wi wal
      wn cab wfo wex df32lem12 abeq2i con2bii biimpi syl con4i ssriv fin23lem41
      dffin3-2 eqssi df-fin2ds eqtri ) DEFAGHBGZICGZJUPKUQUPKLCFMNUPOZPURQRBSAU
      ADEBDEUPEQZUPDQZUSTUPFUQUBCUCZUTTZCBUDVAVBUTVAVATBDBCULUEUFUGUHUIUJUKUMAB
      CUNUO $.
      $( [7-Nov-2014] $)

    ${
      dff34lem.a $e |- F = ( f e. ~P g |-> ( g \ f ) ) $.
      $d F a b c d e $.  $d a b c d e f g $.  $d A a b c d e $.
      $( Lemma for ~ dffin3-4 . $)
      dff34lem1 $p |- ( A e. ~P g -> ( F ` A ) = ( g \ A ) ) $=
        ( va cdif cpw difeq2 cmpt cbvmptv eqtri cvv wcel vex difexg ax-mp fvmpt
        cv ) FACSZFSZGZTAGZTHZDUAATIDBUDTBSZGZJFUDUBJEBFUDUFUBUEUATIKLTMNUCMNCO
        TAMPQR $.
        $( [7-Nov-2014] $)

      $( Lemma for ~ dffin3-4 . $)
      dff34lem2 $p |- F : ~P g --> ~P g $=
        ( cv cdif cpw wcel wral wf wss difss vex elpw2 mpbir rgenw fmpt mpbi )
        BEZAEZFZSGZHZAUBIUBUBCJUCAUBUCUASKSTLUASBMNOPAUBUBUACDQR $.
        $( [7-Nov-2014] $)

      $( Lemma for ~ dffin3-4 . $)
      dff34lem3 $p |- ( A C_ ~P g -> ( F " ( F " A ) ) = A ) $=
        ( va cv cpw wss cima wceq cfv wfn mp2an ffn ax-mp wcel cdif dff34lem1
        wf ccom imaco cid cres wral wb dff34lem2 fco fnresi eqfnfv2 mpan fveq2d
        fvco4 difss vex elpw2 mpbir a1i elpwi dfss4 sylib 3eqtrd fvresi mprgbir
        syl eqtrd eqtr4d imaeq1i resiima syl5eq syl5eqr ) ACGZHZIZDDAJJDDUAZAJZ
        ADDAUBVNVPUCVMUDZAJAVOVQAVOVQKZFGZVOLZVSVQLZKZFVMVOVMMZVQVMMVRWBFVMUEUF
        VMVMVOTZWCVMVMDTZWEWDBCDEUGZWFVMVMVMDDUHNVMVMVOOPVMUIFVMVOVQUJNVSVMQZVT
        VSWAWGVTVSDLZDLZVLVSRZDLZVSDVMMZWGVTWIKWEWLWFVMVMDOPVMDDVSUMUKWGWHWJDVS
        BCDESULWGWKVLWJRZVSWGWJVMQZWKWMKWNWGWNWJVLIVLVSUNWJVLCUOUPUQURWJBCDESVE
        WGVSVLIWMVSKVSVLUSVSVLUTVAVFVBVMVSVCVGVDVHVMAVIVJVK $.
        $( [7-Nov-2014] $)

      $( Lemma for ~ dffin3-4 . $)
      dff34lem4 $p |- ( ( A C_ ~P g /\ A =/= (/) ) ->
          ( F ` U. A ) = |^| ( F " A ) ) $=
        ( va vb vc cv wss wa cdif wcel wel wn wi ex elpw2 wceq sylib cpw c0 wne
        cuni crab cint cfv cima wral simplrr simprl ad2antrr simpr eldif elunii
        sylanbrc syl2anc mt3d expr ralrimiva n0 difss mpbir difeq2 eleq1d eleq2
        wex vex imbi12d rcla4v ax-mp ssel2 dfss4 eqeltrd eldifi embantd exlimdv
        a1i syl5 syl5bi imp eluni wrex ad2ant2rl elndif ad2antrl notbid rcla4ev
        annim rexnal con2d jcad impbid elintrab 3bitr4g eqrdv sspwuni dff34lem1
        jca bitr4i sylbi adantr cmpt cbvmptv eqtri compss inteqd 3eqtr4d ) ACIZ
        UAZJZAUBUCZKZXIAUDZLZXIFIZLZAMZFXJUEZUFZXNDUGZDAUHZUFZXMGXOXTXMGCNZGIZX
        NMZOZKZXRGFNZPZFXJUIZYEXOMYEXTMXMYHYKXMYHYKXMYHKZYJFXJYLXPXJMZXRYIYLYMX
        RKZKZYIYFXMYDYGYNUJYOYIOZYFYOYPKZYEXQMZXRYFYQYDYPYRYLYDYNYPXMYDYGUKULYO
        YPUMYEXIXPUNUPYLYMXRYPUJYEXQAUOUQQURUSUTQXMYKYDYGXKXLYKYDPZXLHIZAMZHVGX
        KYSHAVAXKUUAYSHXKUUAYSYKXIXIYTLZLZAMZYEUUBMZPZXKUUAKZYDUUBXJMZYKUUFPUUH
        UUBXIJXIYTVBUUBXICVHZRVCZYJUUFFUUBXJXPUUBSZXRUUDYIUUEUUKXQUUCAXPUUBXIVD
        VEXPUUBYEVFVIZVJVKUUGUUDUUEYDUUGUUCYTAUUGYTXIJZUUCYTSUUGYTXJMUUMAXJYTVL
        YTXIUUIRTYTXIVMTXKUUAUMVNZUUEYDPUUGYEXIYTVOVRVPVSQVQVTWAXMYFYKYFGHNZUUA
        KZHVGXMYKOZHYEAWBXMUUPUUQHXMUUPUUQXMUUPKZYJOZFXJWCZUUQUURUUHUUFOZUUTUUH
        UURUUJVRUURUUDUUEOZKUVAUURUUDUVBXKUUAUUDXLUUOUUNWDUUOUVBXMUUAYEYTXIWEWF
        WSUUDUUEWITUUSUVAFUUBXJUUKYJUUFUULWGWHUQYJFXJWJTQVQVTWKWLWMYEXIXNUNXRFY
        EXJGVHWNWOWPXKYAXOSZXLXKXNXJMZUVCXKXNXIJUVDAXIWQXNXIUUIRWTXNBCDEWRXAXBX
        KYCXTSXLXKYBXSGFXIDADBXJXIBIZLZXCGXJXIYELZXCEBGXJUVFUVGUVEYEXIVDXDXEUUI
        XFXGXBXH $.
        $( [7-Nov-2014] $)

      $( Lemma for ~ dffin3-4 . $)
      dff34lem5 $p |- ( ( A C_ ~P g /\ A =/= (/) ) ->
          ( F ` |^| A ) = U. ( F " A ) ) $=
        ( wss c0 wne cint cfv cima cuni wceq eqcomd fveq2d ax-mp cin sylib cdif
        sylibr cv cpw wa dff34lem3 adantr inteqd crn imassrn wf dff34lem2 sstri
        frn cdm incom fdmi sseq2i biimpri df-ss syl5eq neeq1d biimpar necon3bii
        imadisj dff34lem4 sylancr 0elpw f0cli a1i dff34lem1 uniss unipw sseqtri
        wcel syl vex elpw2 difeq2d dfss4 3eqtrd ) ACUAZUBZFZAGHZUCZAIZDJDDAKZKZ
        IZDJWFLZDJZDJZWIWDWEWHDWDAWGWDWGAWBWGAMWCABCDEUDUENUFOWDWHWJDWDWJWHWDWF
        WAFZWFGHZWJWHMWFDUGZWADAUHWAWADUIWNWAFBCDEUJZWAWADULPUKZWDDUMZAQZGHZWMW
        BWSWCWBWRAGWBWRAWQQZAWQAUNWBAWQFZWTAMXAWBWQWAAWAWADWOUOUPUQAWQURRUSUTVA
        WFGWRGDAVCVBTWFBCDEVDVENOWDWKVTWJSZVTVTWISZSZWIWDWJWAVMZWKXBMXEWDWAWAWI
        DWOVTVFVGVHWJBCDEVIVNWDWJXCVTWDWIWAVMZWJXCMWDWIVTFZXFXGWDWIWALZVTWLWIXH
        FWPWFWAVJPVTVKVLVHZWIVTCVOVPTWIBCDEVIVNVQWDXGXDWIMXIWIVTVRRVSVS $.
        $( [7-Nov-2014] $)

      $( Lemma for ~ dffin3-4 . $)
      dff34lem6 $p |- Fin3 = { g | A. a ( ( a : om --> ~P g /\
          A. b e. om ( a ` b ) C_ ( a ` suc b ) ) -> U. ran a e. ran a ) } $=
        ( vc com cfv wss wral wa cint wcel wi cuni sseq12d eleq12d wceq c0 csuc
        cfin3 cv cpw wf crn wal cab dffin3-3 ccom weq feq1 ralbidv anbi12d rneq
        fveq1 inteqd imbi12d cbvalv wfun cvv dff34lem2 ax-mp vex cofunexg mp2an
        ffun cla4v sylbi fco mpan adantr cdif sscon wfn ffn fvco4 sylan ffvelrn
        peano2 dff34lem1 syl eqtrd sylan2 syl5ibr ralimdva imp jca cima cdm frn
        rncoss sseqtr4i sstri a1i funfvima2 sylancr rnco2 inteqi fveq2i imassrn
        fdmi wne cin incom syl6sseqr df-ss sylib syl5eq fdm peano1 ne0i eqnetrd
        dm0rn0 necon3bii imadisj sylibr dff34lem5 unieqd imaeq2i sylibd embantd
        dff34lem3 syl5com syl2an sylibrd unieqi dff34lem4 impbii abbii eqtri
        a5i ) UBHBUCZUDZDUCZUEZEUCZUAZYOIZYQYOIZJZEHKZLZYOUFZMZUUDNZOZDUGZBUHYP
        YTYSJZEHKZLZUUDPZUUDNZOZDUGZBUHBDEUIUUHUUOBUUHUUOUUGUUNDUUHHYNCYOUJZUEZ
        YRUUPIZYQUUPIZJZEHKZLZUUPUFZMZUVCNZOZUUKUUMUUHHYNGUCZUEZYRUVGIZYQUVGIZJ
        ZEHKZLZUVGUFZMZUVNNZOZGUGUVFUUGUVQDGDGUKZUUCUVMUUFUVPUVRYPUVHUUBUVLHYNY
        OUVGULZUVRUUAUVKEHUVRYSUVIYTUVJYRYOUVGUPZYQYOUVGUPZQUMUNUVRUUEUVOUUDUVN
        UVRUUDUVNYOUVGUOZUQUWBRURUSUVQUVFGUUPCUTZYOVANUUPVANYNYNCUEZUWCABCFVBZY
        NYNCVGVCZDVDCYOVAVEVFZUVGUUPSZUVMUVBUVPUVEUWHUVHUUQUVLUVAHYNUVGUUPULZUW
        HUVKUUTEHUWHUVIUURUVJUUSYRUVGUUPUPZYQUVGUUPUPZQUMUNUWHUVOUVDUVNUVCUWHUV
        NUVCUVGUUPUOZUQUWLRURVHVIUUKUVBUVEUUMUUKUUQUVAYPUUQUUJUWDYPUUQUWEHYNYNC
        YOVJVKZVLYPUUJUVAYPUUIUUTEHUUIUUTYPYQHNZLZYMYSVMZYMYTVMZJYTYSYMVNUWOUUR
        UWPUUSUWQUWNYPYRHNZUURUWPSYQVTZYPUWRLZUURYSCIZUWPYPYOHVOZUWRUURUXASZHYN
        YOVPZHCYOYRVQZVRUWTYSYNNZUXAUWPSZHYNYRYOVSZYSABCFWAZWBWCWDUWOUUSYTCIZUW
        QYPUXBUWNUUSUXJSUXDHCYOYQVQVRZUWOYTYNNUXJUWQSHYNYQYOVSYTABCFWAWBZWCQWEW
        FWGWHYPUVEUUMOUUJYPUVEUVDCIZCUVCWIZNZUUMYPUWCUVCCWJZJZUVEUXOOUWFUXQYPUV
        CCUFZUXPCYOWLUXRYNUXPUWDUXRYNJUWEYNYNCWKVCZYNYNCUWEXBZWMWNWOZUVCUVDCWPW
        QYPUXMUULUXNUUDYPUXMCCUUDWIZWIZPZUULYPUXMUYBMZCIZUYDUVDUYECUVCUYBCYOWRZ
        WSWTYPUYBYNJZUYBTXCZUYFUYDSUYBUXRYNCUUDXAUXSWNZYPUXPUUDXDZTXCUYIYPUYKUU
        DTYPUYKUUDUXPXDZUUDUXPUUDXEYPUUDUXPJUYLUUDSYPUUDYNUXPHYNYOWKZUXTXFUUDUX
        PXGXHXIYPYOWJZTXCUUDTXCYPUYNHTHYNYOXJHTXCZYPTHNUYOXKHTXLVCWOXMUYNTUUDTY
        OXNXOXHXMUYBTUYKTCUUDXPXOXQZUYBABCFXRWQXIYPUYCUUDYPUUDYNJUYCUUDSUYMUUDA
        BCFYCWBZXSWCYPUXNUYCUUDUVCUYBCUYGXTUYQXIZRYAVLYBYDYLUUNUUGDUUOUUQUUSUUR
        JZEHKZLZUVCPZUVCNZOZUUCUUFUUOUVHUVJUVIJZEHKZLZUVNPZUVNNZOZGUGVUDUUNVUJD
        GUVRUUKVUGUUMVUIUVRYPUVHUUJVUFUVSUVRUUIVUEEHUVRYTUVJYSUVIUWAUVTQUMUNUVR
        UULVUHUUDUVNUVRUUDUVNUWBXSUWBRURUSVUJVUDGUUPUWGUWHVUGVUAVUIVUCUWHUVHUUQ
        VUFUYTUWIUWHVUEUYSEHUWHUVJUUSUVIUURUWKUWJQUMUNUWHVUHVUBUVNUVCUWHUVNUVCU
        WLXSUWLRURVHVIUUCVUAVUCUUFUUCUUQUYTYPUUQUUBUWMVLYPUUBUYTYPUUAUYSEHUWOUU
        AUXJUXAJZUYSUUAVUKUWOUWQUWPJYSYTYMVNUWOUXJUWQUXAUWPUXLUWOUXFUXGUWNYPUWR
        UXFUWSUXHWDUXIWBQWEUWOUUSUXJUURUXAUXKYPUXBUWRUXCUWNUXDUWSUXEYEQYFWFWGWH
        YPVUCUUFOUUBYPVUCVUBCIZUXNNZUUFYPUWCUXQVUCVUMOUWFUYAUVCVUBCWPWQYPVULUUE
        UXNUUDYPVULUYCMZUUEYPVULUYBPZCIZVUNVUBVUOCUVCUYBUYGYGWTYPUYHUYIVUPVUNSU
        YJUYPUYBABCFYHWQXIYPUYCUUDUYQUQWCUYRRYAVLYBYDYLYIYJYK $.
        $( [7-Nov-2014] $)
    $}


    $( Weakly Dedekind-infinite sets are exactly those with an ` om ` -indexed
       ascending chain of subsets. $)
    dffin3-4 $p |- Fin3 = { g | A. a ( ( a : om --> ~P g /\
        A. b e. om ( a ` b ) C_ ( a ` suc b ) ) -> U. ran a e. ran a ) } $=
      ( vc cv cpw cdif cmpt eqid dff34lem6 ) DADAEZFKDEGHZBCLIJ $.
      $( [7-Nov-2014] $)

  $}

  ${
    $d H a b c $.  $d R a b c $.  $d S a b c $.  $d K a b c $.  $d A a b c $.
    $d B a b c $.  $d X a b c $.
    $( Induced isomorphism on a subset. $)
    isores3 $p |- ( ( H Isom R , S ( A , B ) /\ K C_ A /\ X = ( H " K ) ) ->
        ( H |` K ) Isom R , S ( K , X ) ) $=
      ( va vb wiso wa wf1o cv wbr cfv wb wral ssralv wcel fvres cima wceq f1of1
      wss cres wf1 f1ores expcom syl5 adantr breqan12d adantll biimprd ralimdva
      wi bibi2d syld anim12d df-iso 3imtr4g impcom isoeq5 syl5ibrcom 3impia ) A
      BCDEJZFAUDZGEFUAZUBZFGCDEFUEZJZVEVFKVJVHFVGCDVIJZVFVEVKVFABELZHMZIMZCNZVM
      EOZVNEOZDNZPZIAQZHAQZKFVGVILZVOVMVIOZVNVIOZDNZPZIFQZHFQZKVEVKVFVLWBWAWHVL
      ABEUFZVFWBABEUCWIVFWBABFEUGUHUIVFWAVTHFQWHVTHFARVFVTWGHFVFVMFSZKZVTVSIFQZ
      WGVFVTWLUOWJVSIFARUJWKVSWFIFWKVNFSZKZWFVSWNWEVRVOWJWMWEVRPVFWJWMWCVPWDVQD
      VMFETVNFETUKULUPUMUNUQUNUQURHIABCDEUSHIFVGCDVIUSUTVAFGVGCDVIVBVCVD $.
      $( [5-Nov-2014] $)
  $}

  ${
    $d x y z a b c d e f g $.

    $( Every I-finite set is Ia-finite. $)
    fin11a $p |- Fin C_ Fin1a $=
      ( va vb vc cfn cfin1a cv wcel cun wceq cin c0 wa wn wex unfir con3i eleq1
      simpld notbid syl5ibr imp ad2ant2r exlimivv con2i df-fin1a abeq2i sylibr
      ssriv ) ADEAFZDGZUIBFZCFZHZIZUKULJKIZLUKDGZMZULDGZMZLLZCNBNZMZUIEGVAUJUTU
      JMZBCUNUQVCUOUSUNUQVCUQVCUNUMDGZMVDUPVDUPURUKULORPUNUJVDUIUMDQSTUAUBUCUDV
      BAEABCUEUFUGUH $.
      $( [30-Oct-2014] $)

    $( A set is finite in the usual sense iff the power set of its power set is
       Dedekind finite.  This provides an alternate proof of ~ fineqv . $)
    dffin1-2 $p |- Fin = { x | ~P ~P x e. Fin4 } $=
      ( va vb vc vd ve cfn cv cpw cfin4 wcel com cdom wbr wn cen wa ex syl wi
      cab vex pwex wceq breq2 notbid dffin4-2 elab2 pweq pweqd eleq1d elab pwfi
      weq bitri isfinite1 sbth ancoms con3d imp sylbi con2i cvv crab wss ssrab2
      elpw2 mpbir a1i12 wb wex wral isinf ra4 adantrd anim1i breq1 elrab sylibr
      biimpri eximi eleq2 biimpcd adantl simprbi ensym entr sylan syl2an nneneq
      biimpd ad2antlr 3syld exlimdv mpd rabbidv impbid1 impbii con2bii 3bitr4ri
      dom3d mpi eqriv ) BGAHZIZIZJKZAUAZBHZIZIZJKZLXKMNZOZXIXHKXIGKZLCHZMNZOXNC
      XKJXJXIBUBZUCZUCZXPXKUDXQXMXPXKLMUEUFCUGUHXGXLAXIXRABUNZXFXKJYAXEXJXDXIUI
      UJUKULXMXOXMXOOZXOXMXOXKGKZXNXOXJGKYCXIUMXJUMUOYCXKLMNZLXKPNZOZQXNXKUPYDY
      FXNYDXMYEYDXMYEXMYDYELXKUQURRUSUTSVAVBYBXKVCKXMXTYBCDLXKEHZXPPNZEXJVDZYGD
      HZPNZEXJVDZVCYBXPLKZYIXKKZYNYIXJVEYHEXJVFYIXJXSVGVHVIYBYMYJLKZQZYIYLUDZCD
      UNZVJYBYPQZYQYRYSFHZYIKZFVKZYQYRTZYSYTXIVEZYTXPPNZQZFVKZUUBYBYPUUGYBYMUUG
      YOYBUUGCLVLYMUUGTFXICVMUUGCLVNSVOUTUUFUUAFUUFYTXJKZUUEQUUAUUDUUHUUEUUHUUD
      YTXIXRVGVTVPYHUUEEYTXJYGYTXPPVQVRZVSWASYSUUAUUCFYSUUAUUCYSUUAQYQYTYLKZXPY
      JPNZYRUUAYQUUJTYSYQUUAUUJYIYLYTWBWCWDUUAUUJUUKTYSUUAUUJUUKUUAUUEYTYJPNZUU
      KUUJUUAUUHUUEUUIWEUUJUUHUULYKUULEYTXJYGYTYJPVQVRWEUUEXPYTPNUULUUKYTXPCUBW
      FXPYTYJWGWHWIRWDYPUUKYRTYBUUAYPUUKYRXPYJWJWKWLWMRWNWOYRYHYKEXJXPYJYGPUEWP
      WQRXAXBWRWSWTXC $.
      $( [3-Nov-2014] $)

    $( A set is I-finite iff every system of subsets contains a maximal
       subset. $)
    dffin1-3 $p |- Fin = { x | `' {C.} Fr ~P x } $=
      ( va vc vb vd cfn cv cpw crpss wfr wcel wbr wn vex wa wss wne elin adantr
      c0 ccnv cab wpo porpss cnvpo mpbi pwfi biimpi frfi sylancr wral wrex pwex
      cin cvv inex2 inss2 0fin 0elpw mpbir2an ne0i fri mpanr12 mpan weq wpss wi
      ax-mp simprbi elpwi df-pss simplbi2 3syl wel wex csn cun inss1 sseli snfi
      pssnel unfi sylancl elpw2 sylib snssi ad2antrl unssd sylibr sylanbrc wceq
      disjsn biimpri snnz disjpss ad2antll snex unex brcnv brrpss bitri rcla4ev
      breq1 syl2anc dfrex2 ex exlimdv syl5 syld necon4ad imp eqeltrrd rexlimiva
      syl impbii wb pweq freq2 elab bitr4i eqriv ) BFAGZHZIUAZJZAUBZBGZFKZYGHZY
      DJZYGYFKYHYJYHYIYDUCZYIFKZYJYIIUCYKYIUDYIIUEUFYHYLYGUGUHYIYDUIUJYJCGZDGZY
      DLZMCFYIUNZUKZDYPULZYHYPUOKZYJYRYIFYGBNZUMUPYSYJOYPYIPYPTQZYRFYIUQTYPKZUU
      AUUBTFKTYIKTFYIRURYGUSUTYPTVAVHDCYIYPUOYDVBVCVDYQYHDYPYNYPKZYQOYNYGFUUCYQ
      DBVEUUCYQYNYGUUCYNYGQZYNYGVFZYQMZUUCYNYIKZYNYGPZUUDUUEVGUUCYNFKZUUGYNFYIR
      VIZYNYGVJUUEUUHUUDYNYGVKVLVMUUEEBVNZEDVNMZOZEVOUUCUUFEYNYGWAUUCUUMUUFEUUC
      UUMUUFUUCUUMOZYOCYPULZUUFUUNYNEGZVPZVQZYPKZUURYNYDLZUUOUUNUURFKZUURYIKZUU
      SUUNUUIUUQFKUVAUUCUUIUUMYPFYNFYIVRVSZSUUPVTYNUUQWBWCUUNUURYGPUVBUUNYNUUQY
      GUUCUUHUUMUUCUUGUUHUUJYNYGYTWDWESUUKUUQYGPUUCUULUUPYGWFWGWHUURYGYTWDWIUUR
      FYIRWJUUNYNUURVFZUUTUULUVDUUCUUKUULYNUUQUNTWKZUUQTQUVDUVEUULYNUUPWLWMUUPE
      NWNYNUUQWOWCWPUUTYNUURILUVDUURYNIYNUUQDNZUUPWQWRZUVFWSYNUURUVGWTXAWIYOUUT
      CUURYPYMUURYNYDXCXBXDYOCYPXEWEXFXGXHXIXJXKUUCUUIYQUVCSXLXMXNXOYEYJAYGYTAB
      VEYCYIWKYEYJXPYBYGXQYCYIYDXRXNXSXTYA $.
      $( [4-Nov-2014] $)

    $( A set is I-finite iff every system of subsets contains a minimal
       subset. $)
    dffin1-4 $p |- Fin = { x | {C.} Fr ~P x } $=
      ( va vb cfn cpw crpss wfr cab ccnv wcel cdif cmpt wiso eqid vex compssiso
      cv wb isofr ax-mp weq wceq pweq freq2 elab dffin1-3 abeq2i 3bitr4ri eqriv
      syl ) BDAQZEZFGZAHZBQZEZFGZUPFIZGZUOUNJUODJUPUPFURCUPUOCQKLZMUQUSRCUOUTUT
      NBOZPUPUPFURUTSTUMUQAUOVAABUAULUPUBUMUQRUKUOUCULUPFUDUJUEUSBDBUFUGUHUI $.
      $( [4-Nov-2014] $)

    $( Every II-finite set is III-finite. $)
    fin23 $p |- Fin2 C_ Fin3 $=
      ( cfin2 cfin2ds cfin3 fin23lem40 fin23lem41 sstri ) ABCDEF $.
      $( [2-Nov-2014] $)

    $( Every III-finite set is IV-finite. $)
    fin34 $p |- Fin3 C_ Fin4 $=
      ( va vb cfin3 cfin4 cv cpw wcel com cdom wbr vex pwex wceq breq2 dffin4-2
      wn notbid elab2 csdm abeq2i domsdomtr mpan2 sdomdom con3i df-fin3 3imtr4i
      canth2 syl sylbi ssriv ) ACDAEZFZDGZHUKIJZPZUKCGUKDGUMHULIJZPZUOHBEZIJZPU
      QBULDUKAKZLURULMUSUPURULHINQBORUNUPUNHULSJZUPUNUKULSJVAUKUTUGHUKULUAUBHUL
      UCUHUDUIUMACAUETUOADAOTUFUJ $.
      $( [30-Oct-2014] $)

    $( Alternate definition of V-finite which emphasizes the idempotent
       behavior of V-infinite sets. $)
    dffin5-2 $p |- Fin5 = { x | -. ( x =/= (/) /\ x ~~ ( x +c x ) ) } $=
      ( va cfin5 cv c0 wne ccda co cen wbr wa wn cab csdm wo wcel wceq en0 biid
      necon2bbii bitri cdom brsdom cdadom3 mpbiran orbi12i ianor bitr4i df-fin5
      vex abeq2i weq neeq1 id oveq12 anidms breq12d anbi12d notbid elab 3bitr4i
      eqriv ) BCADZEFZVCVCVCGHZIJZKZLZAMZBDZEIJZVJVJVJGHZNJZOZVJEFZVJVLIJZKZLZV
      JCPVJVIPVNVOLZVPLZOVRVKVSVMVTVKVJEQVSVJRVOVJEVOSTUAVMVJVLUBJVTVJVLUCVJVJB
      UJZWAUDUEUFVOVPUGUHVNBCBUIUKVHVRAVJWAABULZVGVQWBVDVOVFVPVCVJEUMWBVCVJVEVL
      IWBUNWBVEVLQVCVJVCVJGUOUPUQURUSUTVAVB $.
      $( [30-Oct-2014] $)

    $( Every IV-finite set is V-finite: if we can pack two copies of the set
       into itself, we can certainly leave space. $)
    fin45 $p |- Fin4 C_ Fin5 $=
      ( va vb vc cfin4 cfin5 cv wpss cen wbr wa wex wn wne ccda c1o cxp c2o wss
      wcel ax-mp c0 co csuc sssucid df-2o sseqtr4i xpss2 a1i wel cop 1onn elexi
      n0 com sucid eleqtrri jctr opelxp sylibr nnord ordirr intnan mtbir nelne1
      word sylancl exlimiv sylbi necomd df-pss sylanbrc vex psseq2i sylib xp1en
      xp2cda entr mpan xpex wceq psseq1 breq1 anbi12d cla4ev syl2an wi cvv ovex
      ensym infpssen1 adantl mpd con3i df-fin4 abeq2i dffin5-2 3imtr4i ssriv )
      ADEBFZAFZGWSWTHIJBKZLZWTUAMZWTWTWTNUBZHIZJZLZWTDSWTESXFXAXFCFZXDGZXHXDHIZ
      JZCKZXAXCWTOPZXDGZXMXDHIZXLXEXCXMWTQPZGZXNXCXMXPRZXMXPMXQXRXCOQRXROOUCZQO
      UDUEUFOQWTUGTUHXCXPXMXCBAUIZBKXPXMMZBWTUMXTYABXTWSOUJZXPSZYBXMSZLYAXTXTOQ
      SZJYCXTYEOXSQOOUNUKULZUOUEUPUQWSOWTQYFURUSYDXTOOSZJYGXTOVEZYGLOUNSYHUKOUT
      TOVATVBWSOWTOYFURVCYBXPXMVDVFVGVHVIXMXPVJVKXPXDXMWTAVLZVPVMVNXMWTHIXEXOWT
      YIVOXMWTXDVQVRXKXNXOJCXMWTOYIYFVSXHXMVTXIXNXJXOXHXMXDWAXHXMXDHWBWCWDWEXEX
      LXAWFZXCXEXDWTHIWTWGSYJWTXDWTWTNWHWIYICBXDWTWJVFWKWLWMXBADABWNWOXGAEAWPWO
      WQWR $.
      $( [30-Oct-2014] $)

    $( Every V-finite set is VI-finite because multiplication dominates
       addition for cardinals. $)
    fin56 $p |- Fin5 C_ Fin6 $=
      ( va cfin5 cfin6 cv cen wbr csdm wo cxp wcel wn cdom wi c2o cfn com ax-mp
      con0 cvv abeq2i c0 ccda co c1o w3o 3mix1 vex xp2cda wb cin onfin2 eqsstri
      inss2 2onn sselii fidomtri sdom2en01 xchbinx xpdom2 sylbir syl5eqbrr xpex
      wa sdomdomtr expcom com12 orrd df-3or sylibr jaoi df-fin5 df-fin6 3imtr4i
      syl ssriv ) ABCADZUAEFZVPVPVPUBUCZGFZHZVQVPUDEFZVPVPVPIZGFZUEZVPBJVPCJVQW
      DVSVQWAWCUFVSVQWAHZWCHWDVSWEWCWEKZVSWCWFVRWBLFZVSWCMWFVRVPNIZWBLVPAUGZUHW
      FNVPLFZWHWBLFWJVPNGFZWENOJWJWKKUIPONPROUJOUKROUMULUNUONVPUPQVPWIUQURNVPVP
      WIWIUSUTVAVSWGWCWBSJVSWGVCWCMVPVPWIWIVBVPVRWBSVDQVEVNVFVGVQWAWCVHVIVJVTAB
      AVKTWDACAVLTVMVO $.
      $( [29-Oct-2014] $)

    $( Every VI-finite set is VII-finite.  Uses Infinity inessentially; I have
       a modified version of ~ infxpen which allows this to be Infinity-free
       like the others, if there is interest. $)
    fin67 $p |- Fin6 C_ Fin7 $=
      ( va vb cfin6 cfin7 cv c0 cen wbr c1o csdm con0 com wn wcel cfn notbid wb
      cvv enfi mpan cxp w3o cdif wrex wa eldif onfin biimpar vex syl5ibrcom imp
      sylbi 0fin mpbiri nsyl 1onn nnsdom isfinite2 sdomirr eldifi omelon ontri1
      mp2b wss infxpen syl2anc sdomen2 sylancr mtbiri sdomen1 xpex anidms bitrd
      3ioran syl3anbrc rexlimiva con2i df-fin6 abeq2i df-fin7 3imtr4i ssriv
      xpen ) ACDAEZFGHZWDIGHZWDWDWDUAZJHZUBZWDBEZGHZBKLUCZUDZMZWDCNWDDNWMWIWKWI
      MZBWLWJWLNZWKUEZWEMWFMWHMZWOWQWDONZWEWPWKWSMZWPWTWKWJONZMZWPWJKNZWJLNZMZU
      EZXBWJKLUFZXCXBXEXCXAXDWJUGPUHULWKWSXAWJRNZWKWSXAQBUIZWDWJRSTPUJUKZWEWSFO
      NZUMXKWEWSXKQUMWDFOSTUNUOWQWSWFXJWFWSIONZILNILJHXLUPIUQIURVCZXLWFWSXLQXMW
      DIOSTUNUOWPWKWRWPWRWKWJWJWJUAZJHZMWPXOWJWJJHZWJUSWPXHXNWJGHZXOXPQXIWPXCLW
      JVDZXQWJKLUTWPXFXRXGXCXRXELKNXCXRXEQVALWJVBTUHULWJVEVFXNWJWJRVGVHVIWKWHXO
      WKWHWJWGJHZXOXHWKWHXSQXIWDWJWGRVJTWKXNRNWGXNGHZXSXOQWJWJXIXIVKWKXTWDWJWDW
      JXIXIWCVLWGXNWJRVGVHVMPUJUKWEWFWHVNVOVPVQWIACAVRVSWNADABVTVSWAWB $.
      $( [29-Oct-2014] $)

    $( Once we allow AC, the "strongest" definition becomes equivalent to the
       "weakest" and the entire hierarchy collapses. $)
    fin71ac $p |- Fin7 C_ Fin $=
      ( va vb cfin7 cfn cv cen wbr con0 com cdif wrex wn wcel numth2 vex reximi
      wo ensym cun wceq wb uncom wss omsson undif mpbi eqtri rexeq ax-mp bitr3i
      rexun biimpi mp2b ori df-fin7 abeq2i isfi 3imtr4i ssriv ) ACDAEZBEZFGZBHI
      JZKZLZVBBIKZUTCMUTDMVDVFVAUTFGZBHKVBBHKZVDVFQZBUTNVGVBBHVAUTAORPVHVIVHVBB
      VCISZKZVIVJHTVKVHUAVJIVCSZHVCIUBIHUCVLHTUDIHUEUFUGVBBVJHUHUIVBBVCIUKUJULU
      MUNVEACABUOUPBUTUQURUS $.
      $( [29-Oct-2014] $)
  $}

  ${
    fin1a2lem.a $e |- S = ( x e. On |-> suc x ) $.

    $d S a b c $.  $d A a b c $.  $d x a b c $.

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem1 $p |- ( A e. On -> ( S ` A ) = suc A ) $=
      ( va con0 wcel csuc wa cfv wceq suceloni ancli cv suceq cmpt eqtri fvmptg
      cbvmptv syl ) BFGZUABHZFGZIBCJUBKUAUCBLMEBENZHZUBFFCUDBOCAFANZHZPEFUEPDAE
      FUGUEUFUDOSQRT $.
      $( [7-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem2 $p |- S : On -1-1-> On $=
      ( va vb con0 wf1 wf cv cfv wceq weq wi wral dff13 csuc wcel suceloni rgen
      fin1a2lem1 fmpt mpbi wa eqeqan12d suc11 bitrd biimpd rgen2a mpbir2an ) FF
      BGFFBHZDIZBJZEIZBJZKZDELZMZEFNDFNDEFFBOAIZPZFQZAFNUJUTAFURRSAFFUSBCUAUBUQ
      DEFUKFQZUMFQZUCZUOUPVCUOUKPZUMPZKUPVAVBULVDUNVEAUKBCTAUMBCTUDUKUMUEUFUGUH
      UI $.
      $( [7-Nov-2014] $)
  $}

  ${
    fin1a2lem.b $e |- E = ( x e. om |-> ( 2o .o x ) ) $.

    $d E a b c d $.  $d x a b c d $.  $d A a b c d $.
    $( Lemma for ~ fin1a2 . $)
    fin1a2lem3 $p |- ( A e. om -> ( E ` A ) = ( 2o .o A ) ) $=
      ( va c2o cv comu co com oveq2 cmpt cbvmptv eqtri ovex fvmpt ) EBFEGZHIZFB
      HIJCQBFHKCAJFAGZHIZLEJRLDAEJTRSQFHKMNFBHOP $.
      $( [7-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem4 $p |- E : om -1-1-> om $=
      ( va vb com cv cfv wceq wral c2o comu co wcel fin1a2lem3 con0 c0 a1i nnon
      c1o wf1 wf wi dff13 2onn nnmcl mpan rgen fmpt mpbi wa eqeqan12d wb adantr
      weq 2on adantl csuc 0lt1o elelsuc ax-mp df-2o eleqtrri omcan bitrd biimpd
      syl31anc rgen2a mpbir2an ) FFBUAFFBUBZDGZBHZEGZBHZIZDEUOZUCZEFJDFJDEFFBUD
      KAGZLMZFNZAFJVJVTAFKFNVRFNVTUEKVRUFUGUHAFFVSBCUIUJVQDEFVKFNZVMFNZUKZVOVPW
      CVOKVKLMZKVMLMZIZVPWAWBVLWDVNWEAVKBCOAVMBCOULWCKPNZVKPNZVMPNZQKNZWFVPUMWG
      WCUPRWAWHWBVKSUNWBWIWAVMSUQWJWCQTURZKQTNQWKNUSQTUTVAVBVCRKVKVMVDVGVEVFVHV
      I $.
      $( [7-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem5 $p |- ( A e. om -> ( A e. ran E <-> -. suc A e. ran E ) ) $=
      ( va com wcel c2o cv wceq wn wb ax-mp fvelrnb eqcom eqeq2d syl5bb rexbiia
      wrex bitri comu co csuc crn cfv wfn wf1 fin1a2lem4 f1fn fin1a2lem3 notbii
      nneob 3bitr4g ) BFGBHEIZUAUBZJZEFSZBUCZUOJZEFSZKBCUDZGZURVAGZKEBULVBUNCUE
      ZBJZEFSZUQCFUFZVBVFLFFCUGVGACDUHFFCUIMZEFBCNMVEUPEFVEBVDJUNFGZUPVDBOVIVDU
      OBAUNCDUJZPQRTVCUTVCVDURJZEFSZUTVGVCVLLVHEFURCNMVKUSEFVKURVDJVIUSVDUROVIV
      DUOURVJPQRTUKUM $.
      $( [7-Nov-2014] $)

    $d S a b $.
    fin1a2lem.aa $e |- S = ( x e. On |-> suc x ) $.
    $( Lemma for ~ fin1a2 .  Establish that ` om ` can be broken into two
       equipollent pieces. $)
    fin1a2lem6 $p |- ( S |` ran E ) : ran E -1-1-onto-> ( om \ ran E ) $=
      ( va vb wf1o com con0 wf1 mp2an wceq wb wrex wcel wa eleq1 c0 ax-mp wf cv
      crn cima cres cdif wss fin1a2lem2 fin1a2lem4 f1f frn omsson syl6ss f1ores
      mp2b cfv wn csuc sseli fin1a2lem1 eqeq1d rexbiia peano2 fin1a2lem5 biimpd
      syl mpcom jca notbid anbi12d syl5ibcom rexlimiv wne simpl c2o comu peano1
      fin1a2lem3 om0x eqtri wfun cdm f1fun f1dm eleqtrri fvelrn eqeltrri mpbiri
      co necon3bi adantl nnsuc syl2anc simplr mpbird anbi1d imbi1d com12 simprr
      wi impr eqcomd ex reximdv2 mpd impbii bitri wfn f1fn fvelimab eldif eqriv
      3bitr4i f1oeq3 mpbi ) CUCZBXPUDZBXPUEZHZXPIXPUFZXRHZJJBKZXPJUGZXSABEUHZII
      CKZIICUAZYCACDUIZIICUJZYFXPIJIICUKZULUMUOZJJXPBUNLXQXTMXSYANFXQXTGUBZBUPZ
      FUBZMZGXPOZYMIPZYMXPPZUQZQZYMXQPZYMXTPYOYKURZYMMZGXPOZYSYNUUBGXPYKXPPZYLU
      UAYMUUDYKJPYLUUAMXPJYKYJUSAYKBEUTVFVAVBUUCYSUUBYSGXPUUDUUAIPZUUAXPPZUQZQZ
      UUBYSUUDUUEUUGUUDYKIPZUUEXPIYKYEYFXPIUGYGYHYIUOUSZYKVCVFUUIUUDUUGUUJUUIUU
      DUUGAYKCDVDZVEVGVHUUBUUEYPUUGYRUUAYMIRUUBUUFYQUUAYMXPRVIVJVKVLYSYMUUAMZGI
      OZUUCYSYPYMSVMZUUMYPYRVNYRUUNYPYQYMSYMSMYQSXPPSCUPZSXPUUOVOSVPWIZSSIPUUOU
      UPMVQASCDVRTVOVSVTCWAZSCWBZPUUOXPPYEUUQYGIICWCTSIUURVQYEUURIMYGIICWDTWESC
      WFLWGYMSXPRWHWJWKGYMWLWMYSUULUUBGIXPYSUUIUULQZUUDUUBQYSUUSQZUUDUUBYSUUIUU
      LUUDUULYSUUIQZUUDUULUVAUUDWTUUHUUIQZUUDWTUVBUUDUUGUUEUUGUUIWNUUIUUDUUGNUU
      HUUKWKWOUULUVAUVBUUDUULYSUUHUUIUULYPUUEYRUUGYMUUAIRUULYQUUFYMUUAXPRVIVJWP
      WQWHWRXAUUTYMUUAYSUUIUULWSXBVHXCXDXEXFXGBJXHZYCYTYONYBUVCYDJJBXITYJGJXPYM
      BXJLYMIXPXKXMXLXQXTXPXRXNTXO $.
      $( [7-Nov-2014] $)

    $( Lemma for ~ fin1a2 .  Split a III-infinite set in two pieces. $)
    fin1a2lem7 $p |- ( -. b e. Fin3 -> E. a ( a C_ b /\ -. a e. Fin3 /\
        -. ( b \ a ) e. Fin3 ) ) $=
      ( vc vd cfin3 wcel wn com wfo wex wss cima wceq syl cvv cdif w3a dffin3-2
      cv abeq2i con2bii ccnv crn imassrn wf fof cdm dfdm4 syl5eqr syl5sseq cres
      fdm ccom wf1 wf1o fin1a2lem4 f1cnv f1ofo mp2b wfun fofun cnvimass sylancl
      fores wb f1f foimacnv mpan2 foeq3 mpbid foco sylancr ax-mp resex cofunexg
      frn mp2an foeq1 cla4ev cnvexg imaexg foeq2 exbidv notbid elab2 fin1a2lem6
      vex sylib f1ocnv difss syl5sseqr syl2anc funcnvcnv imadif imaeq2d fimacnv
      3syl difeq1d 3eqtr3rd difexg sseq1 eleq1 difeq2 3anbi123d syl3anc exlimiv
      eleq1d sylbir ) EUDZJKZLXNMHUDZNZHOZDUDZXNPZXSJKZLZXNXSUAZJKZLZUBZDOZXOXR
      XRLEJEHUCUEUFXQYGHXQXPUGZCUHZQZXNPZYJJKZLZXNYJUAZJKZLZYGXQYHUHZYJXNYHYIUI
      XQXNMXPUJZYQXNRXNMXPUKZYRYQXPULZXNXPUMXNMXPUQZUNSUOXQYJMXSNZDOZYMXQYJMCUG
      ZXPYJUPZURZNZUUCXQYIMUUDNZYJYIUUENZUUGMMCUSZYIMUUDUTUUHACFVAZMMCVBYIMUUDV
      CVDZXQYJXPYJQZUUENZUUIXQXPVEZYJYTPUUNXNMXPVFZXPYIVGYJXPVIVHXQUUMYIRZUUNUU
      IVJXQYIMPZUUQUUJMMCUJUURUUKMMCVKMMCWAVDXNMYIXPVLVMUUMYIYJUUEVNSVOYJYIMUUD
      UUEVPVQUUBUUGDUUFUUDVEZUUETKUUFTKUUHUUSUULYIMUUDVFVRXPYJHWLZVSUUDUUETVTWB
      YJMXSUUFWCWDSYLUUCIUDZMXSNZDOZLZUUCLIYJJXPTKYHTKYJTKUUTXPTWEYHYITWFVDZUVA
      YJRZUVCUUCUVFUVBUUBDUVAYJMXSWGWHWIIDUCZWJUFWMXQYNMXSNZDOZYPXQYNMUUDBYIUPZ
      UGZURZXPYNUPZURZNZUVIXQMYIUAZMUVLNZYNUVPUVMNZUVOUUHUVPYIUVKNZUVQUULYIUVPU
      VJUTUVPYIUVKUTUVSABCFGWKYIUVPUVJWNUVPYIUVKVCVDUVPYIMUUDUVKVPWBZXQYNXPYNQZ
      UVMNZUVRXQUUOYNYTPUWBUUPXQXNYNYTXNYJWOXQYRYTXNRYSUUASWPYNXPVIWQXQUWAUVPRU
      WBUVRVJXQXPYHUVPQZQZXPYHMQZYJUAZQUVPUWAXQUWCUWFXPXQUUOYHUGVEUWCUWFRUUPXPW
      RMYIYHWSXBWTXQUVPMPUWDUVPRMYIWOXNMUVPXPVLVMXQUWFYNXPXQUWEXNYJXQYRUWEXNRYS
      XNMXPXASXCWTXDUWAUVPYNUVMVNSVOYNUVPMUVLUVMVPVQUVHUVODUVNUVLVEZUVMTKUVNTKU
      VQUWGUVTUVPMUVLVFVRXPYNUUTVSUVLUVMTVTWBYNMXSUVNWCWDSYOUVIUVDUVILIYNJXNTKY
      NTKEWLXNYJTXEVRUVAYNRZUVCUVIUWHUVBUVHDUVAYNMXSWGWHWIUVGWJUFWMYFYKYMYPUBDY
      JUVEXSYJRZXTYKYBYMYEYPXSYJXNXFUWIYAYLXSYJJXGWIUWIYDYOUWIYCYNJXSYJXNXHXLWI
      XIWDXJXKXM $.
      $( [7-Nov-2014] $)
  $}

  ${
    $d a A b c d e f g h i $.  $d a B b c d e f g h i $.
    $( Lemma for ~ fin1a2 .  Split a III-infinite set in two pieces. $)
    fin1a2lem8 $p |- ( -. b e. Fin3 -> E. a ( a C_ b /\ -. a e. Fin3 /\
        -. ( b \ a ) e. Fin3 ) ) $=
      ( vc con0 cv csuc cmpt com c2o comu co eqid fin1a2lem7 ) CCDCEZFGZCHINJKG
      ZABPLOLM $.
      $( [7-Nov-2014] $)

    $( Lemma for ~ fin1a2 .  In a chain of finite sets, initial segments are
       finite. $)
    fin1a2lem9 $p |- ( ( {C.} Or a /\ a C_ Fin /\ A e. om ) ->
        { b e. a | b ~<_ A } e. Fin ) $=
      ( vc vd cv cfn wss com wcel cdom wbr con0 sseldi 3ad2ant3 ccrd wa syl2anc
      cfv wb crpss wor w3a csuc crab cin onfin2 inss2 eqsstri cvv vex rabex wel
      peano2 breq1 elrab simprr simpl2 simprl sseldd simpl3 ficarddom ex cardnn
      mpbid sseq2d cardon nnon onsssuc sylancr bitrd sylibd syl5bi ssrab2 sseli
      wceq weq ssel anim12d imp 3ad2antl2 sorpssi 3ad2antl1 cen ficarden adantr
      wo fin23lem25 3expa biimpd sylbid fveq2 impbid1 syl2ani dom2d mpi domfi
      wi ) BFZUAUBZWSGHZAIJZUCZAUDZGJZCFZAKLZCWSUEZXDKLZXHGJXBWTXEXAXBIGXDIMGUF
      GUGMGUHUIZAUNNOXCXHUJJXIXGCWSBUKULXCDEXHXDDFZPSZEFZPSZUJXKXHJZDBUMZXKAKLZ
      QZXCXLXDJZXGXQCXKWSXFXKAKUOUPXCXRXLAPSZHZXSXCXRYAXCXRQZXQYAXCXPXQUQYBXKGJ
      ZAGJXQYATYBWSGXKWTXAXBXRURXCXPXQUSUTYBIGAXJWTXAXBXRVANXKAVBRVEVCXBWTYAXST
      XAXBYAXLAHZXSXBXTAXLAVDVFXBXLMJAMJYDXSTXKVGAVHXLAVIVJVKOVLVMXOXCXPEBUMZXL
      XNVPZDEVQZTZXMXHJXHWSXKXGCWSVNZVOXHWSXMYIVOXCXPYEQZYHXCYJQZYFYGYKYCXMGJZQ
      ZXKXMHXMXKHWGZYFYGWRXAWTYJYMXBXAYJYMXAXPYCYEYLWSGXKVRWSGXMVRVSVTWAWTXAYJY
      NXBWSXKXMWBWCYMYNQZYFXKXMWDLZYGYMYFYPTYNXKXMWEWFYOYPYGYCYLYNYPYGTXKXMWHWI
      WJWKRXKXMPWLWMVCWNWOWPXDXHWQR $.
      $( [8-Nov-2014] $)

    $( Lemma for ~ fin1a2 .  A nonempty finite union of members of a chain is a
       member of the chain. $)
    fin1a2lem10 $p |- ( ( A =/= (/) /\ A e. Fin /\ {C.} Or A ) ->
        U. A e. A ) $=
      ( va vb vc c0 wne wcel crpss wor cuni wi cun neeq1 soeq2 unieq id eleq12d
      wceq imbi12d wa cfn cv csn weq wn eqidd necon1ai w3a vex unisn snid uneq1
      eqeltri uncom un0 eqtri syl6eq unieqd mpbiri a1d adantl simpr simpl2 soss
      wss ssun1 mpsyl uniun uneq2i wo simprr elun1 ad2antll sselii a1i syl12anc
      ssun2 sorpssi ssequn1 eleq1 syl5ibr sylbi impcom syl5eqel syl2anc embantd
      jaodan expr pm2.61dane 3exp com24 findcard2 com12 3imp ) AEFZAUAGZAHIZAJZ
      AGZWPWOWQWSKZBUBZEFZXAHIZXAJZXAGZKZKEEFZEHIZEJZEGZKZKCUBZEFZXLHIZXLJZXLGZ
      KZKZXLDUBZUCZLZEFZYAHIZYAJZYAGZKZKWOWTKBCDAXAERZXBXGXFXKXAEEMYGXCXHXEXJXA
      EHNYGXDXIXAEXAEOYGPQSSBCUDZXBXMXFXQXAXLEMYHXCXNXEXPXAXLHNYHXDXOXAXLXAXLOY
      HPQSSXAYARZXBYBXFYFXAYAEMYIXCYCXEYEXAYAHNYIXDYDXAYAXAYAOYIPQSSXAARZXBWOXF
      WTXAAEMYJXCWQXEWSXAAHNYJXDWRXAAXAAOYJPQSSXKEEXKUEEUFUGXLUAGZYCYBXRYEYKYCY
      BXRYEKZYKYCYBUHZYLXLEXLERZYLYMYNYEXRYNYEXTJZXTGYOXSXTXSDUIZUJZXSYPUKZUMYN
      YDYOYAXTYNYAXTYNYAEXTLZXTXLEXTULYSXTELXTEXTUNXTUOUPUQZURYTQUSUTVAYMXMTZXM
      XQYEYMXMVBUUAXNXPYEXLYAVEUUAYCXNXLXTVFYKYCYBXMVCXLYAHVDVGYMXMXPYEYMXMXPTZ
      TZYDXOXSLZYAYDXOYOLUUDXLXTVHYOXSXOYQVIUPUUCXPXOXSVEZXSXOVEZVJZUUDYAGZYMXM
      XPVKUUCYCXOYAGZXSYAGZUUGYKYCYBUUBVCXPUUIYMXMXOXLXTVLZVMUUJUUCXTYAXSXTXLVQ
      YRVNZVOYAXOXSVRVPXPUUEUUHUUFUUEXPUUHUUEUUDXSRZXPUUHKXOXSVSXPUUHUUMUUJUUJX
      PUULVOUUDXSYAVTWAWBWCXPUUFTUUDXSXOLZYAXOXSUNUUFXPUUNYAGZUUFUUNXORZXPUUOKX
      SXOVSXPUUOUUPUUIUUKUUNXOYAVTWAWBWCWDWGWEWDWHWFWFWIWJWKWLWMWN $.
      $( [8-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem11 $p |- ( ( {C.} Or a /\ a C_ Fin ) -> ran ( b e. om |->
        U. { c e. a | c ~<_ b } ) = ( a u. { (/) } ) ) $=
      ( vd cv crpss cfn wss wa com cdom wbr crab cuni wceq c0 wcel sylibr simpr
      wo wor cmpt crn wrex cab csn cun eqid rnmpt wel unieq syl6eq adantl rabex
      uni0 vex uniex elsnc wne ssrab2 simplll simpllr simplr fin1a2lem9 syl3anc
      olcd soss fin1a2lem10 sseldi orcd pm2.61dane orbi12d syl5ibrcom rexlimdva
      mpsyl eleq1 ccrd cfv sselda ficardom syl ficardid ensym endom breq1 elrab
      3syl sylanbrc elssuni wral simprr adantr domentr syl2anc wb simprl sseldd
      cen sorpssi syl12anc fincssdom mpbid syl5bi ralrimiv unissb eqssd rabbidv
      ex breq2 unieqd eqeq2d rcla4ev elsn peano1 wi dom0 biimpi a1i ssrdv uni0b
      3imtr4g eqcomd sylancr eqeq1 rexbidv jaod impbid syl6bbr abbi1dv syl5eq
      elun ) AEZFUAZYLGHZIZBJCEZBEZKLZCYLMZNZUBZUCDEZYTOZBJUDZDUEYLPUFZUGZBDJYT
      UUAUUAUHUIYOUUDDUUFYOUUDDAUJZUUBUUEQZTZUUBUUFQYOUUDUUIYOUUCUUIBJYOYQJQZIZ
      UUIUUCYTYLQZYTUUEQZTZUUKUUNYSPUUKYSPOZIZUUMUULUUPYTPOZUUMUUOUUQUUKUUOYTPN
      PYSPUKUOULUMYTPYSYRCYLAUPUNUQURRVFUUKYSPUSZIZUULUUMUUSYSYLYTYRCYLUTZUUSUU
      RYSGQZYSFUAZYTYSQUUKUURSUUSYMYNUUJUVAYMYNUUJUURVAZYMYNUUJUURVBYOUUJUURVCY
      QACVDVEYSYLHUUSYMUVBUUTUVCYSYLFVGVOYSVHVEVIVJVKUUCUUGUULUUHUUMUUBYTYLVPUU
      BYTUUEVPVLVMVNYOUUGUUDUUHYOUUGUUDYOUUGIZUUBVQVRZJQZUUBYPUVEKLZCYLMZNZOZUU
      DUVDUUBGQZUVFYOYLGUUBYMYNSVSZUUBVTWAUVDUUBUVIUVDUUBUVHQZUUBUVIHUVDUUGUUBU
      VEKLZUVMYOUUGSUVDUVEUUBWRLZUUBUVEWRLUVNUVDUVKUVOUVLUUBWBWAZUVEUUBDUPWCUUB
      UVEWDWGUVGUVNCUUBYLYPUUBUVEKWEWFWHUUBUVHWIWAUVDYQUUBHZBUVHWJUVIUUBHUVDUVQ
      BUVHYQUVHQBAUJZYQUVEKLZIZUVDUVQUVGUVSCYQYLYPYQUVEKWEWFUVDUVTUVQUVDUVTIZYQ
      UUBKLZUVQUWAUVSUVOUWBUVDUVRUVSWKUVDUVOUVTUVPWLYQUVEUUBWMWNUWAYQGQUVKUVQUU
      BYQHTZUWBUVQWOUWAYLGYQYMYNUUGUVTVBUVDUVRUVSWPZWQUVDUVKUVTUVLWLUWAYMUVRUUG
      UWCYMYNUUGUVTVAUWDYOUUGUVTVCYLYQUUBWSWTYQUUBXAVEXBXHXCXDBUVHUUBXERXFUUCUV
      JBUVEJYQUVEOZYTUVIUUBUWEYSUVHUWEYRUVGCYLYQUVEYPKXIXGXJXKXLWNXHUUHUUBPOZYO
      UUDDPXMYOUUDUWFPYTOZBJUDZYOPJQPYPPKLZCYLMZNZOZUWHXNYOUWKPYOUWJUUEHUWKPOYO
      BUWJUUEYOUVRYQPKLZIZYQPOZYQUWJQYQUUEQUWNUWOXOYOUWMUWOUVRUWMUWOYQXPXQUMXRU
      WIUWMCYQYLYPYQPKWEWFBPXMYAXSUWJXTRYBUWGUWLBPJUWOYTUWKPUWOYSUWJUWOYRUWICYL
      YQPYPKXIXGXJXKXLYCUWFUUCUWGBJUUBPYTYDYEVMXCYFYGUUBYLUUEYKYHYIYJ $.
      $( [8-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem12 $p |- ( ( ( a e. ~P ~P b /\ {C.} Or a /\ -. U. a e. a ) /\
        ( a C_ Fin /\ a =/= (/) ) ) -> -. b e. Fin3 ) $=
      ( vc vd ve vf cv cpw wcel cuni wn wss c0 wa com wi cdom wbr cvv wceq csuc
      crpss wor w3a cfn wne cfv wral crn wal cfin3 wex crab cmpt simpll1 ssrab2
      wf uniss ax-mp sspwuni biimpi syl5ss vex pwex elpw2 3imtr4i syl fmptd wel
      sssucid ssdomg mp2 domtr mpan2 a1i ss2rabi weq breq2 rabbidv unieqd rabex
      uniex fvmpt adantl peano2 3sstr4d ralrimiva csn cun fin1a2lem11 3ad2antl2
      adantrr wo simpl3 simprr uni0c ra4 sylbi simpl simplr simpr eqtr4d simpll
      eqid n0 eqeltrd embantd mpd exlimiv con3d sylc ioran sylanbrc uniun unisn
      ex 0ex uneq2i un0 3eqtri eleq1i elun elsnc orbi2i 3bitri sylnibr unieq id
      eleq12d notbid syl5ibrcom simplrr simpll2 fin1a2lem10 syl3anc cfin4 fveq1
      abeq2i anbi12d sylib mtand dffin1-2 dffin4-2 elab2 reldom brrelexi sylbir
      con2bii sylnbi 3syl feq1 sseq12d ralbidv rneq cla4egv com12 impr syl22anc
      mptexg annim exbii exnal dffin3-4 ) AGZBGZHZHIZUVDUBUCZUVDJZUVDIZKZUDZUVD
      UELZUVDMUFZNZNZOUVFCGZUQZDGZUVQUGZUVSUAZUVQUGZLZDOUHZNZUVQUIZJZUWFIZPZCUJ
      ZUVEUKIUVPUWIKZCULZUWJKUVPUWEUWHKZNZCULZUWLUVPOUVFEOFGZEGZQRZFUVDUMZJZUNZ
      UQZUVSUXAUGZUWAUXAUGZLZDOUHZUXAUIZJZUXGIZKZUXASIZUWOUVPEOUWTUVFUXAUVPUWQO
      IZNUVGUWTUVFIZUVGUVHUVKUVOUXLUOUVDUVFLZUWTUVELUVGUXMUXNUWTUVIUVEUWSUVDLUW
      TUVILUWRFUVDUPUWSUVDURUSUXNUVIUVELUVDUVEUTVAVBUVDUVFUVEBVCZVDVEUWTUVEUXOV
      EVFVGUXAXDZVHUVPUXEDOUVPUVSOIZNZUWPUVSQRZFUVDUMZJZUWPUWAQRZFUVDUMZJZUXCUX
      DUYAUYDLZUXRUXTUYCLUYEUXSUYBFUVDUXSUYBPFAVIUXSUVSUWAQRZUYBUVSSIUVSUWALUYF
      DVCUVSVJUVSUWASVKVLUWPUVSUWAVMVNVOVPUXTUYCURUSVOUXQUXCUYATUVPEUVSUWTUYAOU
      XAEDVQZUWSUXTUYGUWRUXSFUVDUWQUVSUWPQVRVSVTUXPUXTUXSFUVDAVCZWAWBWCWDUXQUXD
      UYDTZUVPUXQUWAOIUYIUVSWEEUWAUWTUYDOUXAUWQUWATZUWSUYCUYJUWRUYBFUVDUWQUWAUW
      PQVRVSVTUXPUYCUYBFUVDUYHWAWBWCVGWDWFWGUVPUXGUVDMWHZWIZTZUXJUVHUVGUVOUYMUV
      KUVHUVMUYMUVNAEFWJWLWKUVPUXJUYMUYLJZUYLIZKUVPUVJUVIMTZWMZUYOUVPUVKUYPKZUY
      QKUVGUVHUVKUVOWNZUVPUVNUVKUYRUVLUVMUVNWOUYSUVNBAVIZBULZUVKUYRPBUVDXEVUAUY
      PUVJUYTUYPUVJPBUYTUYPUVJUYTUYPNZUYTUVEMTZPZUVJUYPVUDUYTUYPVUCBUVDUHVUDBUV
      DWPVUCBUVDWQWRWDVUBUYTVUCUVJUYTUYPWSVUBVUCUVJVUBVUCNZUVIUVEUVDVUEUVIMUVEU
      YTUYPVUCWTVUBVUCXAXBUYTUYPVUCXCXFXPXGXHXPXIXJWRXKUVJUYPXLXMUYOUVIUYLIUVJU
      VIUYKIZWMUYQUYNUVIUYLUYNUVIUYKJZWIUVIMWIUVIUVDUYKXNVUGMUVIMXQXOXRUVIXSXTY
      AUVIUVDUYKYBVUFUYPUVJUVIMUVDUYHWBYCYDYEYFUYMUXIUYOUYMUXHUYNUXGUYLUXGUYLYG
      UYMYHYIYJYKXHUVPUVDUEIZKOSIZUXKUVPVUHUVJUYSUVPVUHNUVNVUHUVHUVJUVLUVMUVNVU
      HYLUVPVUHXAUVGUVHUVKUVOVUHYMUVDYNYOUUAVUHUVDHZHZYPIZVUIVULAUEAUUBYRVULKOV
      UKQRZVUIVULVUMOUVEQRZKVUMKBVUKYPVUJUVDUYHVDVDUVEVUKTVUNVUMUVEVUKOQVRYJBUU
      CUUDUUHOVUKQUUEUUFUUGUUIEOUWTSUUSUUJUXBUXFNZUXJUXKUWOUXKVUOUXJNZUWOUWNVUP
      CUXASUVQUXATZUWEVUOUWMUXJVUQUVRUXBUWDUXFOUVFUVQUXAUUKVUQUWCUXEDOVUQUVTUXC
      UWBUXDUVSUVQUXAYQUWAUVQUXAYQUULUUMYSVUQUWHUXIVUQUWGUXHUWFUXGVUQUWFUXGUVQU
      XAUUNZVTVURYIYJYSUUOUUPUUQUURUWNUWKCUWEUWHUUTUVAYTUWICUVBYTUWJBUKBCDUVCYR
      YF $.
      $( [8-Nov-2014] $)

    $( Lemma for ~ fin1a2 . $)
    fin1a2lem13 $p |- ( ( ( a e. ~P ~P b /\ {C.} Or a /\ -. U. a e. a ) /\
        ( -. c e. Fin /\ c e. a ) ) -> -. ( b \ c ) e. Fin2 ) $=
      ( ve vd vg vf vh cv wcel wn wa c0 wral wrex wceq wss weq eqeq1 sylibr cpw
      crpss wor cuni w3a cfn wel wne cdif cfin2 cab simpl1 vex elpw ssel2 sylib
      wi sylanb ssdif syl sseq1 syl5ibrcom rexlimdva rexbidv elab 3imtr4g ssrdv
      cvv difexg ax-mp pwex elpw2 difidALT eqcomi difeq1 rcla4ev mpan2 0ex ne0i
      eqeq2d ad2antll simpl2 wo cbvrexv sorpssi orim12i orbi12d rexlimdv syl5bi
      sseq2 expr ralrimiv ralbidv sorpss simpl3 uniex syl6bb cbvabv elab2 eqid1
      abrexex adantl elssuni simplr sseqtrd adantll cun unss2 uncom eqtri simp3
      undif1 a1i ad3antrrr simprr ad2antrr simplrr eqid simpllr ssdif0 ad2antlr
      biimpi eqtrd uni0c rcla4va syl2anc ralrimiva unissb eqssd eqeltrd ex mtod
      simpll simplrl syl12anc orel1 sylc undif sseq12d ssun1 sstr mpan syl5 mpd
      syl6bi ad2antrl simprl jca31 annim neeq1 soeq2 anbi12d id eleq12d imbi12d
      unieq notbid rexnal pweq pweqd raleqdv dffin2-3 sylnibr ) AIZBIZUAZUAJZUV
      DUBUCZUVDUDZUVDJZKZUEZCIZUFJKZCAUGZLZLZDIZMUHZUVRUBUCZLZUVRUDZUVRJZUQZDUV
      EUVMUIZUAZUAZNZUWEUJJUVQUWDKZDUWGOZUWHKUVQEIZFIZUVMUIZPZFUVDOZEUKZUWGJZUW
      PMUHZUWPUBUCZLZUWPUDZUWPJZUQZKZUWJUVQUWPUWFQZUWQUVQUVGUXEUVGUVHUVKUVPULUV
      GGUWPUWFUVGGIZUWMPZFUVDOZUXFUWEQZUXFUWPJZUXFUWFJUVGUXGUXIFUVDUVGFAUGZLZUX
      IUXGUWMUWEQZUXLUWLUVEQZUXMUVGUVDUVFQZUXKUXNUVDUVFAUMZUNUXOUXKLUWLUVFJUXNU
      VDUVFUWLUOUWLUVEFUMUNUPURUWLUVEUVMUSUTUXFUWMUWEVAVBVCUWOUXHEUXFGUMZEGRUWN
      UXGFUVDUWKUXFUWMSVDVEZUXFUWEUXQUNVFVGUTUWPUWFUWEUVEVHJUWEVHJBUMZUVEUVMVHV
      IVJZVKVLTUVQUWTUXBKZLUXDUVQUWRUWSUYAUVOUWRUVLUVNUVOMUWPJZUWRUVOMUWMPZFUVD
      OZUYBUVOMUVMUVMUIZPZUYDUYEMUVMVMVNUYCUYFFUVMUVDFCRUWMUYEMUWLUVMUVMVOVTVPV
      QUWOUYDEMVRUWKMPUWNUYCFUVDUWKMUWMSVDVETUWPMVSUTWAUVQUVHUWSUVGUVHUVKUVPWBZ
      UVHUVEUXFQZUXFUVEQZWCZGUWPNZBUWPNUWSUVHUYKBUWPUVEUWPJUVEUWMPZFUVDOZUVHUYK
      UWOUYMEUVEUXSEBRUWNUYLFUVDUWKUVEUWMSVDVEUYMUVEUVRUVMUIZPZDUVDOUVHUYKUYLUY
      OFDUVDFDRUWMUYNUVEUWLUVRUVMVOVTWDUVHUYOUYKDUVDUVHDAUGZLZUYKUYOUYNUXFQZUXF
      UYNQZWCZGUWPNUYQUYTGUWPUXJUXHUYQUYTUXRUYQUXGUYTFUVDUVHUYPUXKUXGUYTUQUVHUY
      PUXKLLZUYTUXGUYNUWMQZUWMUYNQZWCZVUAUVRUWLQZUWLUVRQZWCVUDUVDUVRUWLWEVUEVUB
      VUFVUCUVRUWLUVMUSUWLUVRUVMUSWFUTUXGUYRVUBUYSVUCUXFUWMUYNWJUXFUWMUYNVAWGVB
      WKWHWIWLUYOUYJUYTGUWPUYOUYHUYRUYIUYSUVEUYNUXFVAUVEUYNUXFWJWGWMVBVCWIWIWLB
      GUWPWNTUTUVQUXBUVJUVGUVHUVKUVPWOUXBUXAUXFUVMUIZPZGUVDOZUVQUVJUVRVUGPZGUVD
      OZVUIDUXAUWPUWPFEUVDUWMUXPXAWPUVRUXAPVUJVUHGUVDUVRUXAVUGSVDUWOVUKEDEDRZUW
      OUVRUWMPZFUVDOVUKVULUWNVUMFUVDUWKUVRUWMSVDVUMVUJFGUVDFGRUWMVUGUVRUWLUXFUV
      MVOVTWDWQWRWSUVQVUHUVJGUVDUVQGAUGZVUHUVJUVQVUNVUHLZLZUVIUXFUVDVUPUVIUXFVU
      PHIZUXFQZHUVDNUVIUXFQVUPVURHUVDVUPHAUGZLZVUQUVMUIZVUGQZVURVUOVUSVVBUVQVUO
      VUSLZVVAUXAVUGVVCVVAUWPJZVVAUXAQVVCVVAUWMPZFUVDOZVVDVUSVVFVUOVUSVVAVVAPZV
      VFVVAWTVVEVVGFVUQUVDFHRUWMVVAVVAUWLVUQUVMVOVTVPVQXBUWOVVFEVVAVUQVHJVVAVHJ
      HUMVUQUVMVHVIVJUWKVVAPUWNVVEFUVDUWKVVAUWMSVDVETVVAUWPXCUTVUNVUHVUSXDXEXFV
      VBUVMVVAXGZUVMVUGXGZQZVUTVURVVAVUGUVMXHVUTVVJVUQUVMXGZUXFQZVURVUTVVHVVKVV
      IUXFVVHVVKPVUTVVHVVAUVMXGVVKUVMVVAXIVUQUVMXLXJXMVUTUVMUXFQZVVIUXFPVUTUXFU
      VMQZKVVNVVMWCZVVMVUTVVNUVJUVLUVKUVPVUOVUSUVGUVHUVKXKXNVUTUVOVUHVVNUVJUQUV
      QUVOVUOVUSUVLUVNUVOXOXPZUVQVUNVUHVUSXQUVOVUHLZVVNUVJVVQVVNLZUVIUVMUVDVVRU
      VIUVMVVRUVEUVMQZBUVDNUVIUVMQVVRVVSBUVDVVRBAUGZLZUWEMPZVVSVWAUWEUWPJZUVRMP
      ZDUWPNZVWBVVTVWCVVRVVTUWEUWMPZFUVDOZVWCVVTUWEUWEPZVWGUWEXRVWFVWHFUVEUVDFB
      RUWMUWEUWEUWLUVEUVMVOVTVPVQUWOVWGEUWEUXTUWKUWEPZUWNVWFFUVDUWKUWEUWMSVDVET
      XBVWAUXAMPVWEVWAUXAVUGMUVOVUHVVNVVTXSVVNVUGMPZVVQVVTVVNVWJUXFUVMXTYBYAYCD
      UWPYDUPVWDVWBDUWEUWPUVRUWEMSYEYFUVEUVMXTTYGBUVDUVMYHTVVRUVOUVMUVIQUVOVUHV
      VNYMZUVMUVDXCUTYIVWKYJYKYFYLVUTUVHVUNUVOVVOUVQUVHVUOVUSUYGXPUVQVUNVUHVUSY
      NVVPUVDUXFUVMWEYOVVNVVMYPYQUVMUXFYRUPYSVUQVVKQVVLVURVUQUVMYTVUQVVKUXFUUAU
      UBUUEUUCUUDYGHUVDUXFYHTVUNUXFUVIQUVQVUHUXFUVDXCUUFYIUVQVUNVUHUUGYJWKVCWIY
      LUUHUWTUXBUUIUPUWIUXDDUWPUWGUVRUWPPZUWDUXCVWLUWAUWTUWCUXBVWLUVSUWRUVTUWSU
      VRUWPMUUJUVRUWPUBUUKUULVWLUWBUXAUVRUWPUVRUWPUUPVWLUUMUUNUUOUUQVPYFUWDDUWG
      UURUPUWDDUWKUAZUAZNUWHEUWEUJUXTVWIUWDDVWNUWGVWIVWMUWFUWKUWEUUSUUTUVAEDUVB
      WSUVC $.
      $( [8-Nov-2014] $)

    $( Weak theorem which skips Ia but has a trivial proof, needed to prove
       ~ fin1a2 . $)
    fin12 $p |- Fin C_ Fin2 $=
      ( va vb vc vd cv cpw crpss ccnv wfr cab c0 wne wral wrex wcel wbr cvv vex
      wa wn wor wpss wi cfn cfin2 wss a1i simpll elpwi ad2antlr simprl syl22anc
      brcnv brrpss bitri notbii ralbii rexbii sylib ex ralrimiva ss2abi df-fin2
      fri dffin1-3 3sstr4i ) AEFZGHZIZAJBEZKLZVJGUAZSZCEZDEZUBZTZDVJMZCVJNZUCZB
      VGFZMZAJUDUEVIWBAVIVTBWAVIVJWAOZSZVMVSWDVMSZVOVNVHPZTZDVJMZCVJNZVSWEVJQOZ
      VIVJVGUFZVKWIWJWEBRUGVIWCVMUHWCWKVIVMVJVGUIUJWDVKVLUKCDVGVJQVHVDULWHVRCVJ
      WGVQDVJWFVPWFVNVOGPVPVOVNGDRZCRUMVNVOWLUNUOUPUQURUSUTVAVBAVEABCDVCVF $.
      $( [8-Nov-2014] $)

    $( An II-infinite set can have an I-infinite part broken off and remain
       II-infinite. $)
    fin1a2s $p |- ( -. b e. Fin2 -> E. a ( a C_ b /\ -. a e. Fin /\
        -. ( b \ a ) e. Fin2 ) ) $=
      ( vc cv cfin2 wcel wa cpw wss cfn wn w3a wex cfin3 simpll adantr syl32anc
      simplrr fin23 sseli c0 wne crpss cuni wi wral cdif dffin2-3 abeq2i rexnal
      wrex annim simprlr simpr simprll fin1a2lem12 fin1a2lem8 fin12 sstri con3i
      wor id1 3anim123i eximi 3syl wel nss vex elpw ssel2 sylib sylanb ad2ant2r
      simprr simprl fin1a2lem13 ex eximdv syl5bi imp pm2.61dan syl5bir rexlimiv
      3jca sylbir sylnbi ) BDZEFCDZUAUBZWHUCVAZGZWHUDWHFZUEZCWGHZHZUFZADZWGIZWQ
      JFZKZWGWQUGZEFZKZLZAMZWPBEBCUHUIWPKWMKZCWOUKXEWMCWOUJXFXECWOXFWKWLKZGZWHW
      OFZXEWKWLULXIXHXEXIXHGZWHJIZXEXJXKGZWGNFKZWRWQNFZKZXANFZKZLZAMXEXLXIWJXGX
      KWIXMXIXHXKOXJWJXKXIWIWJXGUMZPXIWKXGXKRXJXKUNXJWIXKXIWIWJXGUOPCBUPQABUQXR
      XDAWRWRXOWTXQXCWRVBWSXNJNWQJENURSUSTUTXBXPENXASTUTVCVDVEXJXKKZXEXTACVFZWT
      GZAMXJXEAWHJVGXJYBXDAXJYBXDXJYBGZWRWTXCXIYAWRXHWTXIWHWNIZYAWRWHWNCVHVIYDY
      AGWQWNFWRWHWNWQVJWQWGAVHVIVKVLVMXJYAWTVNZYCXIWJXGWTYAXCXIXHYBOXJWJYBXSPXI
      WKXGYBRYEXJYAWTVOCBAVPQWDVQVRVSVTWAVQWBWCWEWF $.
      $( [8-Nov-2014] $)

    $( Every Ia-finite set is II-finite. $)
    fin1a2 $p |- Fin1a C_ Fin2 $=
      ( va vb vc vd cfin1a cfin2 cv wcel wn cfn wex wa cun cin c0 sylib vex cvv
      wceq anbi12d wss cdif w3a fin1a2s simpr1 eqcomd disjdif a1i simpr2 simpr3
      undif fin12 sseli nsyl difexg ax-mp weq uneq12 eqeq2d ineq12 eqeq1d eleq1
      notbid bi2anan9 cla42ev syl22anc df-fin1a abeq2i con2bii ex exlimdv con4i
      mpd ssriv ) AEFAGZFHZVOEHZVPIZBGZVOUAZVSJHZIZVOVSUBZFHZIZUCZBKVQIZBAUDVRW
      FWGBVRWFWGVRWFLZVOCGZDGZMZSZWIWJNZOSZLZWIJHZIZWJJHZIZLZLZDKCKZWGWHVOVSWCM
      ZSZVSWCNZOSZWBWCJHZIZXBWHXCVOWHVTXCVOSVRVTWBWEUEVSVOUKPUFXFWHVSVOUGUHVRVT
      WBWEUIWHWDXGVRVTWBWEUJJFWCULUMUNXAXDXFLZWBXHLZLCDVSWCBQVORHWCRHAQVOVSRUOU
      PCBUQZWJWCSZLZWOXIWTXJXMWLXDWNXFXMWKXCVOWIVSWJWCURUSXMWMXEOWIVSWJWCUTVATX
      KWQWBXLWSXHXKWPWAWIVSJVBVCXLWRXGWJWCJVBVCVDTVEVFVQXBXBIAEACDVGVHVIPVJVKVM
      VLVN $.
      $( [8-Nov-2014] $)

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Attic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b A $.  $d a b N $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    jm2.16nn0OLD $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( ( A - 1 ) || (
        ( A rmX N ) - 1 ) /\ ( A - 1 ) || ( ( A rmY N ) - N ) ) ) $=
      ( wcel c1 cmin crmx cdivides wbr crmy cc0 caddc wceq oveq2 oveq1d oveq12d
      co breq2d cz cmul syl2anc va vb cn0 c2 cuz cfv wa cv wi id anbi12d imbi2d
      weq eluzelz peano2zm syl 1z congid sylancl rmx0 breqtrrd 0z rmy0 jca cexp
      w3a 3ad2ant2 simp2 nn0z 3ad2ant1 nn0ssz frmx fovcl sseldi zmulcl mp2an cn
      a1i csquarenn cdif rmspecnonsq eldifi nnz 3syl frmy simp3l iddvds congmul
      syl322anc peano2zdi dvdsmul2 zsscn subid1 sq1 eqcomi oveq2d ax-1cn 3eqtrd
      cc subsq simp3r congadd rmxp1 mulid2i nn0cn addid1i syl6req mulid1 eqcomd
      mul02 rmyp1 3exp a2d nn0ind impcom ) BUCCAUDUEUFZCZADEPZABFPZDEPZGHZXRABI
      PZBEPZGHZUGZXQXRAUAUHZFPZDEPZGHZXRAYFIPZYFEPZGHZUGZUIXQXRAJFPZDEPZGHZXRAJ
      IPZJEPZGHZUGZUIXQXRAUBUHZFPZDEPZGHZXRAUUAIPZUUAEPZGHZUGZUIXQXRAUUADKPZFPZ
      DEPZGHZXRAUUIIPZUUIEPZGHZUGZUIXQYEUIUAUBBYFJLZYMYTXQUUQYIYPYLYSUUQYHYOXRG
      UUQYGYNDEYFJAFMNQUUQYKYRXRGUUQYJYQYFJEYFJAIMUUQUJOQUKULUAUBUMZYMUUHXQUURY
      IUUDYLUUGUURYHUUCXRGUURYGUUBDEYFUUAAFMNQUURYKUUFXRGUURYJUUEYFUUAEYFUUAAIM
      UURUJOQUKULYFUUILZYMUUPXQUUSYIUULYLUUOUUSYHUUKXRGUUSYGUUJDEYFUUIAFMNQUUSY
      KUUNXRGUUSYJUUMYFUUIEYFUUIAIMUUSUJOQUKULYFBLZYMYEXQUUTYIYAYLYDUUTYHXTXRGU
      UTYGXSDEYFBAFMNQUUTYKYCXRGUUTYJYBYFBEYFBAIMUUTUJOQUKULXQYPYSXQXRDDEPZYOGX
      QXRRCZDRCZXRUVAGHXQARCZUVBUDAUNZAUOZUPZUQXRDURUSXQYNDDEAUTNVAXQXRJJEPZYRG
      XQUVBJRCZXRUVHGHUVGVBXRJURUSXQYQJJEAVCNVAVDUUAUCCZXQUUHUUPUVJXQUUHUUPUVJX
      QUUHVFZUULUUOUVKXRUUBASPZAUDVEPZDEPZUUESPZKPZDDSPZJUUASPZKPZEPZUUKGUVKUVB
      UVLRCZUVQRCZUVORCZUVRRCZXRUVLUVQEPGHZXRUVOUVREPGHZXRUVTGHUVKUVDUVBXQUVJUV
      DUUHUVEVGZUVFUPZUVKUUBRCZUVDUWAUVKXQUUARCZUWIUVJXQUUHVHZUVJXQUWJUUHUUAVIV
      JZXQUWJUGUCRUUBVKAUUAUCXPRFVLVMVNTZUWGUUBAVOTUWBUVKUVCUVCUWBUQUQDDVOVPVRU
      VKUVNRCZUUERCZUWCXQUVJUWNUUHXQUVNVQVSVTCUVNVQCUWNAWAUVNVQVSWBUVNWCWDVGZUV
      KXQUWJUWOUWKUWLAUUARXPRIWEVMTZUVNUUEVOTUVKUVIUWJUWDUVIUVKVBVRZUWLJUUAVOTU
      VKUVBUWIUVCUVDUVCUUDXRXRGHZUWEUWHUWMUVCUVKUQVRZUWGUWTUVJXQUUDUUGWFZUVKUVB
      UWSUWHXRWGUPZXRUUBDADWHWIUVKUVBUWNUVIUWOUWJXRUVNJEPZGHUUGUWFUWHUWPUWRUWQU
      WLUVKXRADKPZXRSPZUXCGUVKUXDRCUVBXRUXEGHUVKAUWGWJUWHUXDXRWKTUVKUXCUVNUVMDU
      DVEPZEPZUXEUVKUVNWSCUXCUVNLUVKRWSUVNWLUWPVNUVNWMUPUVKDUXFUVMEDUXFLUVKUXFD
      WNWOVRWPUVKAWSCDWSCUXGUXELUVKRWSAWLUWGVNWQADWTUSWRVAUVJXQUUDUUGXAZXRUVNJU
      UEUUAWHWIXRUVLUVQUVOUVRXBWIUVKUUJUVPDUVSEUVKXQUWJUUJUVPLUWKUWLAUUAXCTUVKU
      VSDJKPDUVKUVQDUVRJKUVQDLUVKDWQXDVRUVKUUAWSCZUVRJLUVJXQUXIUUHUUAXEVJZUUAXJ
      UPODWQXFXGOVAUVKXRUUEASPZUUBKPZUUADSPZDKPZEPZUUNGUVKUVBUXKRCZUXMRCZUWIUVC
      XRUXKUXMEPGHZUUDXRUXOGHUWHUVKUWOUVDUXPUWQUWGUUEAVOTUVKUWJUVCUXQUWLUQUUADV
      OUSUWMUWTUVKUVBUWOUWJUVDUVCUUGUWSUXRUWHUWQUWLUWGUWTUXHUXBXRUUEUUAADWHWIUX
      AXRUXKUXMUUBDXBWIUVKUUMUXLUUIUXNEUVKXQUWJUUMUXLLUWKUWLAUUAXKTUVKUUAUXMDKU
      VKUXMUUAUVKUXIUXMUUALUXJUUAXHUPXINOVAVDXLXMXNXO $.
      $( [1-Oct-2014] $)
  $}
  $( changes of plan: do use Lucas formula, explicit congruence lemmata $)
  ${
    $d a b A $.  $d a b B $.  $d a b N $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    jm2.15nn0OLD $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ( ZZ>= ` 2 ) /\ N e. NN0 )
        -> ( ( A - B ) || ( ( A rmX N ) - ( B rmX N ) ) /\ ( A - B ) || ( ( A
        rmY N ) - ( B rmY N ) ) ) ) $=
      ( wcel cmin co crmx cdivides wbr crmy wa cc0 c1 wceq oveq2 oveq12d breq2d
      cz cmul syl2anc va vb c2 cuz cfv cn0 cv anbi12d imbi2d weq eluzelz zsubcl
      wi caddc syl2an 1z congid sylancl rmx0 oveqan12d breqtrrd 0z rmy0 jca w3a
      cexp adantr 3ad2ant2 adantl simp2l nn0z 3ad2ant1 nn0ssz frmx fovcl sseldi
      zmulcl simp2r cn csquarenn cdif rmspecnonsq eldifi nnz 3syl simp3l iddvds
      syl frmy congmul syl322anc cc zsscn sqcl ax-1cn a1i nnncan2 syl3anc sqval
      eqtrd simp3r congadd rmxp1 rmyp1 3exp a2d nn0ind impcom 3impa ) AUCUDUEZD
      ZBXJDZCUFDZABEFZACGFZBCGFZEFZHIZXNACJFZBCJFZEFZHIZKZXMXKXLKZYCYDXNAUAUGZG
      FZBYEGFZEFZHIZXNAYEJFZBYEJFZEFZHIZKZUMYDXNALGFZBLGFZEFZHIZXNALJFZBLJFZEFZ
      HIZKZUMYDXNAUBUGZGFZBUUDGFZEFZHIZXNAUUDJFZBUUDJFZEFZHIZKZUMYDXNAUUDMUNFZG
      FZBUUNGFZEFZHIZXNAUUNJFZBUUNJFZEFZHIZKZUMYDYCUMUAUBCYELNZYNUUCYDUVDYIYRYM
      UUBUVDYHYQXNHUVDYFYOYGYPEYELAGOYELBGOPQUVDYLUUAXNHUVDYJYSYKYTEYELAJOYELBJ
      OPQUHUIUAUBUJZYNUUMYDUVEYIUUHYMUULUVEYHUUGXNHUVEYFUUEYGUUFEYEUUDAGOYEUUDB
      GOPQUVEYLUUKXNHUVEYJUUIYKUUJEYEUUDAJOYEUUDBJOPQUHUIYEUUNNZYNUVCYDUVFYIUUR
      YMUVBUVFYHUUQXNHUVFYFUUOYGUUPEYEUUNAGOYEUUNBGOPQUVFYLUVAXNHUVFYJUUSYKUUTE
      YEUUNAJOYEUUNBJOPQUHUIYECNZYNYCYDUVGYIXRYMYBUVGYHXQXNHUVGYFXOYGXPEYECAGOY
      ECBGOPQUVGYLYAXNHUVGYJXSYKXTEYECAJOYECBJOPQUHUIYDYRUUBYDXNMMEFZYQHYDXNRDZ
      MRDXNUVHHIXKARDZBRDZUVIXLUCAUKZUCBUKZABULZUOZUPXNMUQURXKXLYOMYPMEAUSBUSUT
      VAYDXNLLEFZUUAHYDUVILRDXNUVPHIUVOVBXNLUQURXKXLYSLYTLEAVCBVCUTVAVDUUDUFDZY
      DUUMUVCUVQYDUUMUVCUVQYDUUMVEZUURUVBUVRXNUUEASFZAUCVFFZMEFZUUISFZUNFZUUFBS
      FZBUCVFFZMEFZUUJSFZUNFZEFZUUQHUVRUVIUVSRDZUWDRDZUWBRDZUWGRDZXNUVSUWDEFHIZ
      XNUWBUWGEFHIZXNUWIHIUVRUVJUVKUVIYDUVQUVJUUMXKUVJXLUVLVGVHZYDUVQUVKUUMXLUV
      KXKUVMVIVHZUVNTZUVRUUERDZUVJUWJUVRXKUUDRDZUWSUVQXKXLUUMVJZUVQYDUWTUUMUUDV
      KVLZXKUWTKUFRUUEVMAUUDUFXJRGVNVOVPTZUWPUUEAVQTUVRUUFRDZUVKUWKUVRXLUWTUXDU
      VQXKXLUUMVRZUXBXLUWTKUFRUUFVMBUUDUFXJRGVNVOVPTZUWQUUFBVQTUVRUWARDZUUIRDZU
      WLUVRXKUWAVSVTWAZDZUXGUXAAWBUXJUWAVSDUXGUWAVSVTWCUWAWDWHWEZUVRXKUWTUXHUXA
      UXBAUUDRXJRJWIVOTZUWAUUIVQTUVRUWFRDZUUJRDZUWMUVRXLUWFUXIDZUXMUXEBWBUXOUWF
      VSDUXMUWFVSVTWCUWFWDWHWEZUVRXLUWTUXNUXEUXBBUUDRXJRJWIVOTZUWFUUJVQTUVRUVIU
      WSUXDUVJUVKUUHXNXNHIZUWNUWRUXCUXFUWPUWQUVQYDUUHUULWFZUVRUVIUXRUWRXNWGWHZX
      NUUEUUFABWJWKUVRUVIUXGUXMUXHUXNXNUWAUWFEFZHIUULUWOUWRUXKUXPUXLUXQUVRXNAAS
      FZBBSFZEFZUYAHUVRUVIUVJUVKUVJUVKUXRUXRXNUYDHIUWRUWPUWQUWPUWQUXTUXTXNABABW
      JWKUVRUYAUVTUWEEFZUYDUVRUVTWLDZUWEWLDZMWLDZUYAUYENUVRAWLDZUYFUVRRWLAWMUWP
      VPZAWNWHUVRBWLDZUYGUVRRWLBWMUWQVPZBWNWHUYHUVRWOWPUVTUWEMWQWRUVRUVTUYBUWEU
      YCEUVRUYIUVTUYBNUYJAWSWHUVRUYKUWEUYCNUYLBWSWHPWTVAUVQYDUUHUULXAZXNUWAUWFU
      UIUUJWJWKXNUVSUWDUWBUWGXBWKUVRUUOUWCUUPUWHEUVRXKUWTUUOUWCNUXAUXBAUUDXCTUV
      RXLUWTUUPUWHNUXEUXBBUUDXCTPVAUVRXNUUIASFZUUEUNFZUUJBSFZUUFUNFZEFZUVAHUVRU
      VIUYNRDZUYPRDZUWSUXDXNUYNUYPEFHIZUUHXNUYRHIUWRUVRUXHUVJUYSUXLUWPUUIAVQTUV
      RUXNUVKUYTUXQUWQUUJBVQTUXCUXFUVRUVIUXHUXNUVJUVKUULUXRVUAUWRUXLUXQUWPUWQUY
      MUXTXNUUIUUJABWJWKUXSXNUYNUYPUUEUUFXBWKUVRUUSUYOUUTUYQEUVRXKUWTUUSUYONUXA
      UXBAUUDXDTUVRXLUWTUUTUYQNUXEUXBBUUDXDTPVAVDXEXFXGXHXI $.
      $( [1-Oct-2014] $)
  $}

  $( adding primes to either side of a GCD never reduces it, under the
     dvds-order. $)
  gcddvdiso1 $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A || B -> ( A gcd C
      ) || ( B gcd C ) ) ) $=
    ( cz wcel w3a cdivides wbr cgcd co wa simpl 3adantl2 gcdcl nn0z 3syl simpl2
    cn0 imp syl32anc simpl3 simpl1 gcddvds syl2anc simpld dvdstr simprd dvdsgcd
    simpr ex ) ADEZBDEZCDEZFZABGHZACIJZBCIJGHZUNUOKZUPDEZULUMUPBGHZUPCGHZUQURUK
    UMKZUPREUSUKUMUOVBULVBUOLMACNUPOPZUKULUMUOQZUKULUMUOUAZURUSUKULUPAGHZUOUTVC
    UKULUMUOUBZVDURVFVAURUKUMVFVAKVGVEACUCUDZUEUNUOUIUSUKULFVFUOKUTUPABUFSTURVF
    VAVHUGUSULUMFUTVAKUQUPBCUHSTUJ $.

  $( [23-Sep-2014] $)
  gcddvdiso2 $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A || B -> ( C gcd A
      ) || ( C gcd B ) ) ) $=
    ( wcel w3a cdivides wbr cgcd gcddvdiso1 wceq gcdcom 3adant2 3adant1 breq12d
    cz co sylibd ) AODZBODZCODZEZABFGACHPZBCHPZFGCAHPZCBHPZFGABCIUAUBUDUCUEFRTU
    BUDJSACKLSTUCUEJRBCKMNQ $.
    $( [23-Sep-2014] $)


$( ---- COMPUTABILITY ---- $)
$( Define Turing machines and computable functions and prove composition laws as needed. Polynomials are computable. $)

$( we're about to use this a ton, so give it a proper name $)

  $c ,n 1st_n 2nd_n $.
  ${
    $( PLEASE PUT DESCRIPTION HERE. $)
    ccantor-pair $a class ,n $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    ccantor-pair-1st $a class 1st_n $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    ccantor-pair-2nd $a class 2nd_n $.
    $d x y $.  $d a b c d e f A $.  $d a b c d e f B $.  $d a b c d e f C $.
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

    $( The cantor pair.  Similar to ~ nn0opth from the core, but with the
       refinement of being onto. $)
    df-cantor-pair $a |- ,n = ( x e. NN0 , y e. NN0 |-> ( ( ( ( x + y ) x. ( (
        x + y ) + 1 ) ) / 2 ) + x ) ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    nn0leadd2 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> A <_ ( A + B ) ) $=
      ( cn0 wcel wa cc0 caddc co cle cc wceq simpl nn0cn addid1 3syl wbr nn0ge0
      adantl cr nn0re wb 0re a1i adantr leadd2 syl3anc mpbid eqbrtrrd ) ACDZBCD
      ZEZAFGHZAABGHZIUKUIAJDULAKUIUJLAMANOUKFBIPZULUMIPZUJUNUIBQRUKFSDZBSDZASDZ
      UNUOUAUPUKUBUCUJUQUIBTRUIURUJATUDFBAUEUFUGUH $.

    $( [6-Sep-2014] $)
    nn0leadd1 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> B <_ ( A + B ) ) $=
      ( cn0 wcel wa cc0 caddc co cle cc cr nn0re adantl recnd addid2 syl nn0ge0
      wceq wbr adantr wb 0re a1i leadd1 syl3anc mpbid eqbrtrrd ) ACDZBCDZEZFBGH
      ZBABGHZIUJBJDUKBRUJBUIBKDZUHBLMZNBOPUJFAISZUKULISZUHUOUIAQTUJFKDZAKDZUMUO
      UPUAUQUJUBUCUHURUIALTUNFABUDUEUFUG $.
      $( [6-Sep-2014] $)

    $( so we don't have to keep proving the same substitutions a billion
       times. $)
    cantor-pair-lem13 $p |- ( A = B -> ( ( A x. ( A + 1 ) ) / 2 ) = ( ( B x. (
        B + 1 ) ) / 2 ) ) $=
      ( wceq c1 caddc co cmul c2 cdiv id1 oveq1 oveq12d oveq1d ) ABCZAADEFZGFBB
      DEFZGFHINABOPGNJABDEKLM $.

    $( [2-Sep-2014] $)
    cantor-pair-lem14 $p |- ( ( A = C /\ B = D ) -> ( ( ( ( A + B ) x. ( ( A +
        B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 )
        + C ) ) $=
      ( wceq wa caddc co c1 cmul c2 cdiv oveq12 cantor-pair-lem13 simpl oveq12d
      syl ) ACEZBDEZFZABGHZUAIGHJHKLHZCDGHZUCIGHJHKLHZACGTUAUCEUBUDEACBDGMUAUCN
      QRSOP $.

    $( [2-Sep-2014] $)
    cantor-pair-value $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A ,n B ) = ( ( ( (
        A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) ) $=
      ( va vb cn0 cv caddc co cmul cdiv ccantor-pair wceq weq cantor-pair-lem14
      c1 c2 equid mpan2 eqid1 mpan df-cantor-pair ovex ovmpt2 ) CDABEECFZDFZGHZ
      UFOGHIHPJHUDGHZABGHZUHOGHIHPJHZAGHZKAUEGHZUKOGHIHPJHAGHZUDALDDMUGULLDQUDU
      EAUENRAALUEBLULUJLASAUEABNTCDUAUIAGUBUC $.

    $( [2-Sep-2014] $)
    cantor-pair-lem3 $p |- ( A e. CC -> ( ( ( A + 1 ) x. ( ( A + 1 ) + 1 ) ) /
        2 ) = ( ( ( A x. ( A + 1 ) ) / 2 ) + ( A + 1 ) ) ) $=
      ( cc wcel c1 caddc co cmul cdiv wceq ax-1cn ax-addass a1i syl3anc syl2anc
      c2 oveq2d oveq1d 3eqtrd ax-mulcl 2ne0 mp3an23 1p1e2apr1 peano2cn ax-distr
      eqtrd id1 2cn ax-mulcom cc0 wne wa jctir divdir divcan4 ) ABCZADEFZUPDEFZ
      GFZOHFAUPGFZUPOGFZEFZOHFZUSOHFZUTOHFZEFZVCUPEFUOURVAOHUOURUPAOEFZGFZUPAGF
      ZUTEFZVAUOUQVFUPGUOUQADDEFZEFZVFUODBCZVLUQVKIJJADDKUAUOVJOAEVJOIUOUBLPUEP
      UOUPBCZUOOBCZVGVIIAUCZUOUFZVNUOUGLZUPAOUDMUOVHUSUTEUOVMUOVHUSIVOVPUPAUHNQ
      RQUOUSBCZUTBCZVNOUIUJZUKVBVEIUOUOVMVRVPVOAUPSNUOVMVNVSVOVQUPOSNUOVNVTVQTU
      LUSUTOUMMUOVDUPVCEUOVMVNVTVDUPIVOVQVTUOTLUPOUNMPR $.

    $( [1-Sep-2014] $)
    cantor-pair-lem4 $p |- ( A = 0 -> ( ( A x. ( A + 1 ) ) / 2 ) = 0 ) $=
      ( cc0 wceq c1 caddc co cmul c2 cdiv oveq1 cc wcel id 0cn eqeltrd ax-addcl
      a1i ax-1cn syl2anc mul02 syl eqtrd oveq1d 2cn 2ne0 div0i syl6eq ) ABCZAAD
      EFZGFZHIFBHIFBUHUJBHIUHUJBUIGFZBABUIGJUHUIKLZUKBCUHAKLDKLZULUHABKUHMBKLUH
      NQOUMUHRQADPSUITUAUBUCHUDUEUFUG $.

    $( [1-Sep-2014] $)
    cantor-pair-lem5 $p |- ( A e. NN0 -> ( ( A x. ( A + 1 ) ) / 2 ) e. NN0 ) $=
      ( vb va cv c1 caddc co cmul c2 cdiv cn0 wcel cc0 cantor-pair-lem13 eleq1d
      wceq weq eqid1 cantor-pair-lem4 adantr ax-mp wa cc nn0cn cantor-pair-lem3
      0nn0 eqeltri syl simpr peano2nn0 nn0addcl syl2anc eqeltrd ex nn0ind ) BDZ
      UPEFGHGIJGZKLMMEFGHGIJGZKLCDZUSEFGZHGIJGZKLZUTUTEFGHGIJGZKLZAAEFGHGIJGZKL
      BCAUPMPUQURKUPMNOBCQUQVAKUPUSNOUPUTPUQVCKUPUTNOUPAPUQVEKUPANOURMKMMPURMPM
      RMSUAUFUGUSKLZVBVDVFVBUBZVCVAUTFGZKVFVCVHPZVBVFUSUCLVIUSUDUSUEUHTVGVBUTKL
      ZVHKLVFVBUIVFVJVBUSUJTVAUTUKULUMUNUO $.
      $( [1-Sep-2014] $)

    $( structurally monotonic. $)
    cantor-pair-lem6 $p |- ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) -> ( ( A x. ( A
        + 1 ) ) / 2 ) <_ ( ( B x. ( B + 1 ) ) / 2 ) ) $=
      ( cn0 wcel cle wbr w3a c1 caddc co cmul c2 cdiv cr cc0 wa jca syl syl2anc
      3syl simp1 nn0re nn0ge0 3ad2ant2 peano2re peano2nn0 simp2 wb 1re a1i 3jca
      simp3 leadd1 mpbid lemul12a imp clt id1 remulcl 2re pm3.2i lediv1 syl3anc
      2pos ) ACDZBCDZABEFZGZAAHIJZKJZBBHIJZKJZEFZVJLMJVLLMJEFZVHANDZOAEFZPZBNDZ
      PZVINDZOVIEFZPZVKNDZPZPZVGVIVKEFZPZVMVHVSWDVHVQVRVHVEVQVEVFVGUAZVEVOVPAUB
      ZAUCQRVFVEVRVGBUBZUDZQVHWBWCVHVTWAVHVEVOVTWHWIAUEZTVHVEVICDWAWHAUFVIUCTQV
      HVFWCVEVFVGUGZVFVRWCWJBUEZRRQQVHVGWFVEVFVGULZVHVGWFWOVHVOVRHNDZGVGWFUHVHV
      OVRWPVHVEVOWHWIRWKWPVHUIUJUKABHUMRUNQWEWGVMABVIVKUOUPSVHVJNDZVLNDZLNDZOLU
      QFZPZVMVNUHVHVEVOWQWHWIVOVOVTWQVOURWLAVIUSSTVHVFVRWRWMWJVRVRWCWRVRURWNBVK
      USSTXAVHWSWTUTVDVAUJVJVLLVBVCUN $.
      $( [1-Sep-2014] $)

    $( ( ( ( A + B ) x.  ( ( A + B ) + 1 ) ) + A ) < ( ( ( A + B ) x.  ( ( A +
       B ) + 1 ) ) + ( ( A + B ) + 1 ) ) = ( ( ( ( A + B ) + 1 ) x.  ( ( ( A +
       B ) + 1 ) + 1 ) ) <= ( ( C + D ) x.  ( ( C + D ) + 1 ) ) <= ( ( ( C +
       D ) x.  ( ( C + D ) + 1 ) ) + C ) $)
    cantor-pair-lem9 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( ( ( ( A + B ) x. ( (
        A + B ) + 1 ) ) / 2 ) + A ) e. NN0 ) $=
      ( cn0 wcel wa caddc co c1 cmul cdiv nn0addcl cantor-pair-lem5 simpr simpl
      c2 syl adantr syl2anc ex mpd ) ACDZBCDZEZABFGZUDHFGIGOJGZCDZUEAFGCDZUCUDC
      DUFABKUDLPUCUFUGUCUFEUFUAUGUCUFMUCUAUFUAUBNQUEAKRST $.
      $( [1-Sep-2014] $)

    $( separation of diagonals lemma: if two values belong to separate
       diagonals, they are not the same. $)
    cantor-pair-lem7 $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e.
        NN0 ) /\ ( A + B ) < ( C + D ) ) ->
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) < ( ( ( ( C + D ) x.
        ( ( C + D ) + 1 ) ) / 2 ) + C ) ) $=
      ( cn0 wcel caddc co clt wbr c1 cmul c2 cdiv cr nn0re 3syl syl cc0 cle w3a
      wa simp1 cantor-pair-lem9 nn0addcl 1nn0 cantor-pair-lem5 simp2 adantr 1re
      sylancl readdcl nn0leadd2 ltp1 lelttrd wb ltadd2 syl3anc mpbid wceq nn0cn
      cc cantor-pair-lem3 breqtrrd 0re simp3 nn0ltp1le syl2anc cantor-pair-lem6
      addid1 simpl nn0ge0 a1i 3jca leadd2 letrd ltletrd ) AEFZBEFZUBZCEFZDEFZUB
      ZABGHZCDGHZIJZUAZWDWDKGHZLHMNHZAGHZWHWHKGHLHMNHZWEWEKGHLHMNHZCGHZWGVTWJEF
      WJOFVTWCWFUCZABUDWJPQWGWHEFZWKEFWKOFWGVTWOWNVTWDEFZKEFWOABUEZUFWDKUEUKRZW
      HUGWKPQZWGWCWMEFWMOFVTWCWFUHZCDUDWMPQZWGVTWJWKIJWNVTWJWIWHGHZWKIVTAWHIJZW
      JXBIJZVTAWDWHVRAOFZVSAPUIZVTWPWDOFZWQWDPZRZVTXGKOFWHOFZXIUJWDKULUKZABUMVT
      WPXGWDWHIJWQXHWDUNQUOVTXEXJWIOFZXCXDUPXFXKVTWPWIEFXLWQWDUGWIPQAWHWIUQURUS
      VTWPWDVBFWKXBUTWQWDVAWDVCQVDRWGWKWLSGHZWMWSWGWLOFZSOFZXMOFWGWCXNWTWCWEEFZ
      WLEFZXNCDUEZWEUGZWLPQZRVEWLSULUKXAWGWKWLXMTWGWOXPWHWETJZWKWLTJWRWGWCXPWTX
      RRZWGWFYAVTWCWFVFWGWPXPWFYAUPWGVTWPWNWQRYBWDWEVGVHUSWHWEVIURWGWLVBFZXMWLU
      TWGXPXQYCYBXSWLVAQWLVJRVDWGSCTJZXMWMTJZWGWCWAYDWTWAWBVKCVLQWGWCXOCOFZXNUA
      YDYEUPWTWCXOYFXNXOWCVEVMWAYFWBCPUIXTVNSCWLVOQUSVPVQ $.
      $( [19-Oct-2014] $)

    $( first, use the trichotomy law to show that they must be in the same
       diagonal, because if > or < the values would be different. then get the
       result by cancellation. $)
    cantor-pair-lem8 $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e.
        NN0 ) /\
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x.
        ( ( C + D ) + 1 ) ) / 2 ) + C ) ) -> ( A = C /\ B = D ) ) $=
      ( cn0 wcel wa caddc co wceq clt wbr wn cr 3syl adantr simpr syl3anc nn0cn
      cc c1 cmul c2 cdiv w3a simp1 nn0addcl nn0re simp2 lttri3 cantor-pair-lem9
      wb syl2anc syl simp3 breq2d mtbid cantor-pair-lem7 mtand breq1d mpbir2and
      eqcomd cantor-pair-lem13 oveq1d eqtrd cantor-pair-lem5 simpl addcan mpbid
      ltnr oveq1 eqcoms sylan9eq 3ad2ant1 adantl 3ad2ant2 ad2antrr jca mpdan )
      AEFZBEFZGZCEFZDEFZGZABHIZWFUAHIUBIUCUDIZAHIZCDHIZWIUAHIUBIUCUDIZCHIZJZUEZ
      WFWIJZACJZBDJZGZWMWNWFWIKLZMZWIWFKLZMZWMWFNFZWINFZWNWSXAGULWMWBWFEFZXBWBW
      EWLUFZABUGZWFUHOWMWEWIEFXCWBWEWLUIZCDUGWIUHOWFWIUJUMWMWRWHWKKLZWMWHWHKLZX
      HWMWHNFZXIMWMWBWHEFXJXEABUKWHUHOWHVJUNZWMWHWKWHKWBWEWLUOZUPUQWMWRGWBWEWRX
      HWMWBWRXEPWMWEWRXGPWMWRQABCDURRUSWMWTWKWHKLZWMXIXMXKWMWHWKWHKXLUTUQWMWTGW
      EWBWTXMWMWEWTXGPWMWBWTXEPWMWTQCDABURRUSVAWMWNGZWOWQXNWHWGCHIZJZWOXNWHWKXO
      WMWLWNXLPXNWJWGCHXNWIWFJWJWGJXNWFWIWMWNQZVBWIWFVCUNVDVEXNWGTFZATFZCTFZXPW
      OULXNWBXDXRWMWBWNXEPXFXDWGEFXRWFVFWGSUNOWMXSWNWMWBVTXSXEVTWAVGASZOPWMXTWN
      WMWEWCXTXGWCWDVGCSOPWGACVHRVIXNWOGZWOWPXNWOQYBWFADHIZJZWPXNWOWFWIYCXQWIYC
      JCACADHVKVLVMWMYDWPULZWNWOWMXSBTFZDTFZYEWBWEXSWLVTXSWAYAPVNWBWEYFWLWAYFVT
      BSVOVNWEWBYGWLWDYGWCDSVOVPABDVHRVQVIVRVSVS $.

    $( [1-Sep-2014] $)
    cantor-pair-lem10 $p |- E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a +
        b ) + 1 ) ) / 2 ) + a ) = 0 $=
      ( cc0 cn0 wcel caddc co c1 cmul c2 cdiv wceq cv wrex 0nn0 cc ax-mp oveq1d
      oveq12d eqeq1d nn0addcli cantor-pair-lem5 nn0cn syl 00id cantor-pair-lem4
      addid1i eqtri oveq1 id oveq2 rcla42ev mp3an ) CDEZUNCCFGZUOHFGZIGZJKGZCFG
      ZCLZAMZBMZFGZVCHFGZIGZJKGZVAFGZCLZBDNADNOOUSURCURUODEZURPEZCCOOUAVIURDEVJ
      UOUBURUCUDQUGUOCLURCLUEUOUFQUHVHUTCVBFGZVKHFGZIGZJKGZCFGZCLABCCDDVACLZVGV
      OCVPVFVNVACFVPVEVMJKVPVCVKVDVLIVACVBFUIZVPVCVKHFVQRSRVPUJSTVBCLZVOUSCVRVN
      URCFVRVMUQJKVRVKUOVLUPIVBCCFUKZVRVKUOHFVSRSRRTULUM $.

    $( [1-Sep-2014] $)
    cantor-pair-lem11 $p |- ( A e. NN0 ->
        ( E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 )
        + a ) = A ->
            E. c e. NN0 E. d e. NN0 ( ( ( ( c + d ) x. ( ( c + d ) + 1 ) ) / 2
        ) + c ) = ( A + 1 ) ) ) $=
      ( cn0 wcel caddc co c1 cmul c2 cdiv wceq cc0 adantr oveq1d ax-1cn eqtrd
      cc cv wrex wa w3a 0nn0 a1i simp3 simpl peano2nn0 3syl simpl2 oveq2d nn0cn
      wi 3ad2ant3 addcom sylancl ax-addass syl3anc 3eqtrd oveq12d nn0addcl 1nn0
      cantor-pair-lem5 addid1 eqtr3d cantor-pair-lem3 adantl eqcomd mpdan simpr
      0cn oveq1 id eqeq1d oveq2 rcla42ev 3exp1 wn cmin cn simp2 wo elnn0 biimpi
      syl orcomd ord mpd nnm1nn0 subcl mpan2 sylancr weq eqid cantor-pair-lem14
      npcan mpan pm2.61d rexlimdvv ) AFGZBUAZCUAZHIZXDJHIZKIZLMIZXBHIZANZDUAZEU
      AZHIZXLJHIZKIZLMIZXJHIZAJHIZNZEFUBDFUBZBCFFXAXCONZXBFGZXCFGZUCZXIXSUNUNXA
      XTYCXIXSXAXTYCUDZXIUCZOFGZXBJHIZFGZOYGHIZYIJHIZKIZLMIZOHIZXQNZXSYFYEUEUFY
      DYHXIYDYCYAYHXAXTYCUGYAYBUHZXBUIZUJPYEYMXEXEJHIZKIZLMIZXGXEHIZXQYEYSOHIZY
      MYSYEYSYLOHYEYRYKLMYEXEYIYQYJKYEXEXBOHIZJHIOXBHIZJHIZYIYEXDUUBJHYEXCOXBHX
      AXTYCXIUKULQYEUUBUUCJHYEXBTGZOTGZUUBUUCNYDUUEXIYCXAUUEXTYAUUEYBXBUMPZUOZP
      ZVLXBOUPUQQYEUUFUUEJTGZUUDYINUUFYEVLUFUUIUUJYERUFOXBJURUSUTZYEXEYIJHUUKQV
      AQQYEYSFGZYSTGUUAYSNYEXEFGZUULYEXDFGZJFGUUMYDUUNXIYCXAUUNXTXBXCVBZUOZPZVC
      XDJVBUQXEVDWFYSUMYSVEUJVFYEUUNXDTGZYSYTNUUQXDUMZXDVGUJYEYTXHJHIZXQYDYTUUT
      NZXIYDUUNUVAUUPYDUUNUCZYTXGXDHIZJHIZUUTUVBXGTGZUURUUJYTUVDNUVBXGFGZUVEUUN
      UVFYDXDVDZVHXGUMZWFUUNUURYDUUSVHUUJUVBRUFUVEUURUUJUDUVDYTXGXDJURVIUSUVBUV
      CXHJHUVBXDXBXGHUVBXDUUBXBUVBXCOXBHXAXTYCUUNUKULUVBUUEUUBXBNYDUUEUUNUUHPXB
      VEWFSULQSVJPYEXHAJHYDXIVKQSUTXRYNOXKHIZUVIJHIZKIZLMIZOHIZXQNDEOYGFFXJONZX
      PUVMXQUVNXOUVLXJOHUVNXNUVKLMUVNXLUVIXMUVJKXJOXKHVMZUVNXLUVIJHUVOQVAQUVNVN
      VAVOXKYGNZUVMYMXQUVPUVLYLOHUVPUVKYKLMUVPUVIYIUVJYJKXKYGOHVPZUVPUVIYIJHUVQ
      QVAQQVOVQUSVRXAXTVSZYCXIXSXAUVRYCUDZXIUCZYHXCJVTIZFGZYGUWAHIZUWCJHIZKIZLM
      IZYGHIZXQNZXSUVSYHXIUVSYCYAYHXAUVRYCUGZYOYPUJPUVSUWBXIUVSXCWAGZUWBUVSUVRU
      WJXAUVRYCWBUVSXTUWJUVSUWJXTYCXAUWJXTWCZUVRYBUWKYAYBUWKXCWDWEVHUOWGWHWIXCW
      JWFPUVTUWCXDNZUWHUVSUWLXIYCXAUWLUVRYCUWCXBJUWAHIZHIZXDYCUUEUUJUWATGZUWCUW
      NNUUGUUJYCRUFZYBUWOYAYBXCTGZUUJUWOXCUMZRXCJWKZUQVHXBJUWAURUSYCUWMXCXBHYCU
      WQUWMXCNYBUWQYAUWRVHUWQUWMUWAJHIZXCUWQUUJUWOUWMUWTNRUWQUUJUWORUWSWLJUWAUP
      WMUWQUUJUWTXCNRXCJWQWLSWFULSUOPUVTUWLUCZUWGXGYGHIZXQUXAUWFXGYGHUXAUWEXFLM
      UXAUWCXDUWDXEKUVTUWLVKZUXAUWCXDJHUXCQVAQQUVTUXBXQNUWLUVTUXBUUTXQUVTYCUXBU
      UTNZUVSYCXIUWIPYCUVEUUEUUJUXDYCUUNUVFUVEUUOUVGUVHUJUUGUWPUVEUUEUUJUDUUTUX
      BXGXBJURVIUSWFUVTXHAJHUVSXIVKQSPSVJXRUWHYGXKHIZUXEJHIKILMIYGHIZXQNDEYGUWA
      FFXJYGNZXPUXFXQUXGEEWNXPUXFNXKWOXJXKYGXKWPWLVOXKUWANZUXFUWGXQYGYGNUXHUXFU
      WGNYGWOYGXKYGUWAWPWRVOVQUSVRWSWT $.

    $( [1-Sep-2014] $)
    cantor-pair-lem12 $p |- ( A e. NN0 -> E. a e. NN0 E. b e. NN0 ( ( ( ( a + b
        ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = A ) $=
      ( ve vf vc vd cv caddc co c1 cmul cdiv wceq cn0 wrex eqeq2 2rexbidv weq
      c2 cantor-pair-lem10 wcel cantor-pair-lem11 eqid cantor-pair-lem14 eqeq1d
      cc0 mpan2 mpan cbvrex2v biimpi syl6 nn0ind ) BHZCHZIJZUPKIJLJTMJUNIJZDHZN
      ZCOPBOPUQUGNZCOPBOPUQEHZNZCOPBOPZUQVAKIJZNZCOPBOPZUQANZCOPBOPDEAURUGNUSUT
      BCOOURUGUQQRDESUSVBBCOOURVAUQQRURVDNUSVEBCOOURVDUQQRURANUSVGBCOOURAUQQRBC
      UAVAOUBVCFHZGHZIJZVJKIJLJTMJVHIJZVDNZGOPFOPZVFVABCFGUCVMVFVLVEUNVIIJZVNKI
      JLJTMJUNIJZVDNFGBCOOFBSZVKVOVDVPGGSVKVONVIUDVHVIUNVIUEUHUFGCSZVOUQVDBBSVQ
      VOUQNUNUDUNVIUNUOUEUIUFUJUKULUM $.

    $( [1-Sep-2014] $)
    cantor-pair-map $p |- ,n : ( NN0 X. NN0 ) --> NN0 $=
      ( va vb cv caddc co cmul cdiv cn0 wcel wral ccantor-pair cantor-pair-lem9
      c1 c2 cxp wf rgen2 df-cantor-pair fmpt2 mpbi ) ACZBCZDEZUCMDEFENGEUADEZHI
      ZBHJAHJHHOHKPUEABHHUAUBLQABHHUDHKABRST $.
      $( [19-Oct-2014] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    cantor-pair $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 )
        /\ ( A ,n B ) = ( C ,n D ) ) -> ( A = C /\ B = D ) ) $=
      ( cn0 wcel wa ccantor-pair co wceq w3a caddc c1 cmul c2 cantor-pair-value
      cdiv simp1 simp2 3ad2ant1 eqcomd 3ad2ant2 3eqtrd cantor-pair-lem8 syl3anc
      simp3 ) AEFBEFGZCEFDEFGZABHIZCDHIZJZKZUGUHABLIZUMMLINIOQIALIZCDLIZUOMLINI
      OQICLIZJACJBDJGUGUHUKRUGUHUKSULUNUIUJUPULUIUNUGUHUIUNJUKABPTUAUGUHUKUFUHU
      GUJUPJUKCDPUBUCABCDUDUE $.

    $( [1-Sep-2014] $)
    cantor-pair-1 $p |- ,n : ( NN0 X. NN0 ) -1-1-> NN0 $=
      ( va vb cn0 cxp ccantor-pair cv cfv wceq wral wcel wa c1st c2nd cop caddc
      co c1 biimpi simpr syl3anc wf1 wf weq dff13 cantor-pair-map cmul cdiv cvv
      wi c2 simpll elxp7 3syl simplr elxp6 ad2antrr ad2antlr simp3 simpl fveq2d
      df-ov cantor-pair-value syl5eqr adantl 3ad2ant1 3ad2ant2 cantor-pair-lem8
      w3a eqtrd 3eqtr3d 1st2nd2 opeq12 simp2 3eqtr4d ex rgen2a mpbir2an ) CCDZC
      EUAVRCEUBAFZEGZBFZEGZHZABUCZUIZBVRIAVRIABVRCEUDUEWEABVRVSVRJZWAVRJZKZWCWD
      WHWCKZVSLGZWALGZHVSMGZWAMGZHKZVSWJWLNZHZWAWKWMNZHZWDWIWJCJWLCJKZWKCJWMCJK
      ZWJWLOPZXAQOPUFPUJUGPWJOPZWKWMOPZXCQOPUFPUJUGPWKOPZHZWNWIWFVSUHUHDZJZWSKZ
      WSWFWGWCUKWFXHVSCCULRXGWSSUMWIWGWAXFJZWTKZWTWFWGWCUNWGXJWACCULRXIWTSUMWIW
      PWSKZWRWTKZWCXEWFXKWGWCWFXKVSCCUORUPWGXLWFWCWGXLWACCUORUQWHWCSXKXLWCVHVTW
      BXBXDXKXLWCURXKXLVTXBHWCXKVTWOEGZXBXKVSWOEWPWSUSUTWSXMXBHWPWSXMWJWLEPXBWJ
      WLEVAWJWLVBVCVDVIVEXLXKWBXDHWCXLWBWQEGZXDXLWAWQEWRWTUSUTWTXNXDHWRWTXNWKWM
      EPXDWKWMEVAWKWMVBVCVDVIVFVJTWJWLWKWMVGTWFWPWGWCVSCCVKUPWGWRWFWCWACCVKUQWN
      WPWRVHWOWQVSWAWNWPWOWQHWRWJWLWKWMVLVEWNWPWRVMWNWPWRURVNTVOVPVQ $.
      $( [19-Oct-2014] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    cantor-pair-o $p |- ,n : ( NN0 X. NN0 ) -onto-> NN0 $=
      ( vc vd va vb cn0 cxp ccantor-pair wfo wf wceq wrex wral dffo3 wcel caddc
      cv cfv co wa ad2antlr cantor-pair-map cmul cdiv cantor-pair-lem12 opelxpi
      c1 c2 cop cantor-pair-value df-ov a1i simpr 3eqtr3rd fveq2 eqeq2d rcla4ev
      syl2anc ex rexlimdvva mpd rgen mpbir2an ) EEFZEGHVCEGIAPZBPZGQZJZBVCKZAEL
      BAVCEGMUAVHAEVDENZCPZDPZORZVLUFORUBRUGUCRVJORZVDJZDEKCEKVHVDCDUDVIVNVHCDE
      EVIVJENVKENSZSZVNVHVPVNSZVJVKUHZVCNZVDVRGQZJZVHVOVSVIVNVJVKEEUETVQVJVKGRZ
      VMVTVDVOWBVMJVIVNVJVKUITWBVTJVQVJVKGUJUKVPVNULUMVGWABVRVCVEVRJVFVTVDVEVRG
      UNUOUPUQURUSUTVAVB $.
      $( [19-Oct-2014] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    cantor-pair-1o $p |- ,n : ( NN0 X. NN0 ) -1-1-onto-> NN0 $=
      ( cn0 cxp ccantor-pair wf1o wf1 wfo cantor-pair-1 cantor-pair-o mpbir2an
      df-f1o ) AABZACDKACEKACFKACJGHI $.

    $( [1-Sep-2014] $)
    cantor-pair-lem19 $p |- ( A e. NN0 -> A <_ ( ( A x. ( A + 1 ) ) / 2 ) ) $=
      ( va vb cv c1 caddc co cmul c2 cdiv cle wbr cc0 wceq id cantor-pair-lem13
      breq12d weq cn0 wcel 0nn0 nn0ge0i eqid1 cantor-pair-lem4 cantor-pair-lem5
      ax-mp breqtrri peano2nn0 nn0leadd1 cc nn0cn cantor-pair-lem3 syl breqtrrd
      syl2anc a1d nn0ind ) BDZURUREFGHGIJGZKLMMMEFGHGIJGZKLCDZVAVAEFGZHGIJGZKLZ
      VBVBVBEFGHGIJGZKLZAAAEFGHGIJGZKLBCAURMNZURMUSUTKVHOURMPQBCRZURVAUSVCKVIOU
      RVAPQURVBNZURVBUSVEKVJOURVBPQURANZURAUSVGKVKOURAPQMMUTKMUAUBMMNUTMNMUCMUD
      UFUGVASTZVFVDVLVBVCVBFGZVEKVLVCSTVBSTVBVMKLVAUEVAUHVCVBUIUOVLVAUJTVEVMNVA
      UKVAULUMUNUPUQ $.

    $( [6-Sep-2014] $)
    cantor-pair-lesum $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A + B ) <_ ( A ,n B
        ) ) $=
      ( cn0 wcel wa caddc co c1 cmul c2 cdiv ccantor-pair cle cr nn0addcl nn0re
      syl cantor-pair-lem5 3syl wbr cantor-pair-value nn0ssre cantor-pair-lem19
      cantor-pair-map fovcl sseldi eqeltrrd simpl nn0leadd2 syl2anc breqtrrd
      letrd ) ACDZBCDZEZABFGZUPUPHFGIGJKGZAFGZABLGZMUOUPUQURUOUPCDZUPNDABOZUPPQ
      UOUTUQCDZUQNDVAUPRZUQPSUOUSURNABUAZUOCNUSUBABCCCLUDUEUFUGUOUTUPUQMTVAUPUC
      QUOVBUMUQURMTUOUTVBVAVCQUMUNUHUQAUIUJULVDUK $.

    $( [6-Sep-2014] $)
    cantor-pair-le1 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> A <_ ( A ,n B ) ) $=
      ( cn0 wcel wa caddc co ccantor-pair nn0re adantr nn0addcl cantor-pair-map
      cr syl fovcl nn0leadd2 cantor-pair-lesum letrd ) ACDZBCDZEZAABFGZABHGZSAM
      DTAIJUAUBCDUBMDABKUBINUAUCCDUCMDABCCCHLOUCINABPABQR $.

    $( [1-Sep-2014] $)
    cantor-pair-fixpoint $p |- ( 0 ,n 0 ) = 0 $=
      ( cc0 ccantor-pair co caddc c1 cmul cdiv wcel wceq 0nn0 cantor-pair-value
      c2 cn0 mp2an 00id cantor-pair-lem4 oveq1d ax-mp eqtri ) AABCZAADCZUAEDCFC
      LGCZADCZAAMHZUDTUCIJJAAKNUCUAAUAAIZUCUAIOUEUBAADUAPQROSS $.

    $( [2-Sep-2014] $)
    cantor-pair-le2 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> B <_ ( A ,n B ) ) $=
      ( cn0 wcel wa caddc co ccantor-pair nn0re adantl nn0addcl cantor-pair-map
      cr syl fovcl nn0leadd1 cantor-pair-lesum letrd ) ACDZBCDZEZBABFGZABHGZTBM
      DSBIJUAUBCDUBMDABKUBINUAUCCDUCMDABCCCHLOUCINABPABQR $.

    $( [6-Sep-2014] $)
    df-cantor-pair-1st $a |- 1st_n = ( 1st o. `' ,n ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-cantor-pair-2nd $a |- 2nd_n = ( 2nd o. `' ,n ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    cantor-pair-lem16 $p |- `' ,n : NN0 --> ( NN0 X. NN0 ) $=
      ( cn0 cxp ccantor-pair wf1o ccnv wf cantor-pair-1o f1ocnv f1of mp2b ) AAB
      ZACDAKCEZDAKLFGKACHAKLIJ $.
      $( [6-Sep-2014] $)

    ${
      cantor-pair-lem17.0 $e |- E = ( A o. `' ,n ) $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      cantor-pair-lem18 $p |- E = ( ( A |` ( NN0 X. NN0 ) ) o. `' ,n ) $=
        ( ccantor-pair ccnv ccom cn0 cxp cres crn wss wceq cantor-pair-map fdmi
        cdm dfdm4 eqtr3i eqimss2i cores ax-mp eqtr4i ) BADEZFZAGGHZIUBFZCUBJZUD
        KUEUCLUDUFDOUDUFUDGDMNDPQRAUBUDSTUA $.
        $( [6-Sep-2014] $)

      cantor-pair-lem17.1 $e |- ( ( B e. NN0 /\ C e. NN0 ) -> ( A ` <. B , C >.
          ) = D ) $.
      cantor-pair-lem17.2 $e |- A : _V -onto-> _V $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      cantor-pair-lem17 $p |- ( ( B e. NN0 /\ C e. NN0 ) -> ( E ` ( B ,n C ) )
          = D ) $=
        ( cn0 wcel wa ccantor-pair co cfv ccnv ccom eqcomi wceq cvv a1i cop cxp
        fveq1i wf wfo fofun ax-mp cantor-pair-lem16 cantor-pair-map fovcl fvco3
        wfun syl3anc df-ov fveq2i wf1o cantor-pair-1o opelxpi f1ocnvfv1 sylancr
        syl5eq fveq2d 3eqtrd syl5eqr ) BIJCIJKZBCLMZENVFALOZPZNZDVFVHEEVHFQUCVE
        VIVFVGNZANZBCUAZANDVEAULZIIIUBZVGUDZVFIJVIVKRVMVESSAUEVMHSSAUFUGTVOVEUH
        TBCIIILUIUJIVNVFAVGUKUMVEVJVLAVEVJVLLNZVGNZVLVFVPVGBCLUNUOVEVNILUPVLVNJ
        VQVLRUQBCIIURVNIVLLUSUTVAVBGVCVD $.
        $( [6-Sep-2014] $)
    $}

    ${
      cantor-pair-lem15.0 $e |- ( NN0 =/= (/) -> ( A |` ( NN0 X. NN0 ) ) : (
          NN0 X. NN0 ) -onto-> NN0 ) $.
      cantor-pair-lem15.1 $e |- B = ( A o. `' ,n ) $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      cantor-pair-lem15 $p |- B : NN0 -onto-> NN0 $=
        ( cn0 wfo cxp cres ccantor-pair ccnv ccom cc0 wcel 0nn0 mp2b wf1o ax-mp
        c0 wne wceq ne0i cantor-pair-1o f1ocnv f1ofo mp2an wb crn wss cdm dfdm4
        foco cantor-pair-map fdmi eqimssi eqsstr3i cores eqtr4i foeq1 mpbir ) E
        EBFZEEAEEGZHZIJZKZFZVAEVBFZEVAVCFZVELEMERSVFNELUACOVAEIPEVAVCPVGUBVAEIU
        CEVAVCUDOEVAEVBVCUKUEBVDTUTVEUFBAVCKZVDDVCUGZVAUHVDVHTVIIUIZVAIUJVJVAVA
        EIULUMUNUOAVCVAUPQUQEEBVDURQUS $.
        $( [6-Sep-2014] $)
    $}
    $( PLEASE PUT DESCRIPTION HERE. $)
    cantor-pair-1stfo $p |- 1st_n : NN0 -onto-> NN0 $=
      ( c1st ccantor-pair-1st cn0 fo1stres df-cantor-pair-1st cantor-pair-lem15
      ) ABCCDEF $.

    $( [6-Sep-2014] $)
    cantor-pair-2ndfo $p |- 2nd_n : NN0 -onto-> NN0 $=
      ( c2nd ccantor-pair-2nd cn0 fo2ndres df-cantor-pair-2nd cantor-pair-lem15
      ) ABCCDEF $.

    $( [6-Sep-2014] $)
    cantor-pair-1op $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( 1st_n ` ( A ,n B ) )
        = A ) $=
      ( c1st ccantor-pair-1st df-cantor-pair-1st cn0 wcel cop cfv op1stg adantr
      wceq fo1st cantor-pair-lem17 ) CABADEAFGABHCIALBFGABFJKMN $.

    $( [6-Sep-2014] $)
    cantor-pair-2op $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( 2nd_n ` ( A ,n B ) )
        = B ) $=
      ( c2nd ccantor-pair-2nd df-cantor-pair-2nd op2ndg fo2nd cantor-pair-lem17
      cn0 ) CABBDEABIIFGH $.

    $( [6-Sep-2014] $)
    cantor-pair-p12 $p |- ( A e. NN0 -> ( ( 1st_n ` A ) ,n ( 2nd_n ` A ) ) = A
        ) $=
      ( va vb vc cn0 wcel cv ccantor-pair cfv ccantor-pair-1st ccantor-pair-2nd
      wceq cxp wrex co wfo cantor-pair-o wa fveq2 sylan9eq foelrn biimpi adantl
      cop elxp2 simpll df-ov a1i 3eqtr4d simplr cantor-pair-1op cantor-pair-2op
      mpan oveq12d simpl eqtr4d syl2anc ex rexlimdvva mpan9 rexlimiva syl ) AEF
      ZABGZHIZLZBEEMZNZAJIZAKIZHOZALZVGEHPVCVHQBVGEAHUAUMVFVLBVGVDVGFZVDCGZDGZU
      DZLZDENCENZVFVLVMVRCDVDEEUEUBVFVQVLCDEEVFVNEFVOEFRZRZVQVLVTVQRZAVNVOHOZLZ
      VSVLWAVEVPHIZAWBVQVEWDLVTVDVPHSUCVFVSVQUFWBWDLWAVNVOHUGUHUIVFVSVQUJWCVSRZ
      VKWBAWEVIVNVJVOHWCVSVIWBJIVNAWBJSVNVOUKTWCVSVJWBKIVOAWBKSVNVOULTUNWCVSUOU
      PUQURUSUTVAVB $.
      $( [6-Sep-2014] $)
  $}

  ${
    $( Facts about map, fz, and mapfz: if you have to use elmap, your subproof should probably be moved here. $)

    $d a b c d e f g h i A $.  $d a b c d e f g h i B $.
    $d a b c d e f g h i C $.  $d a b c d e f g h i D $.
    $d a b c d e f g h i r $.  $d a b c d e f g h i R $.
    $d a b c d e f g h i x $.  $d a b c d e f g h i y $.


    $( could still stand to be shortened but at least it's highly reusable. $)
    elfz-lastp $p |- ( ( A e. ZZ /\ B e. ( 1 ... ( A + 1 ) ) ) ->
        ( B = ( A + 1 ) \/ B e. ( 1 ... A ) ) ) $=
      ( cz wcel c1 co cfz wa wn cle wbr ad2antlr jca wb elfz syl3anc syl2anc cr
      zre 3ad2ant1 caddc wceq simpll elfzelz simplr peano2zdi mpbid simpr mtbid
      elfzel1 w3a simp2r clt simp2l simp3 pm3.2 con3d imp adantr adantl zltp1le
      ltnle mpbird peano2z syl letri3 ex orrd orcomd ) ACDZBEAEUAFZGFDZHZBEAGFD
      ZBVKUBZVMVNVOVMVNIZVOVMVPHZVJBCDZHZEBJKZBVKJKZHZVTBAJKZHZIZVOVQVJVRVJVLVP
      UCZVLVRVJVPBEVKUDLZMVQVLWBVJVLVPUEVQVRECDZVKCDZVLWBNWGVLWHVJVPBEVKUJLZVQA
      WFUFBEVKOPUGVQVNWDVMVPUHVQVRWHVJVNWDNWGWJWFBEAOPUIVSWBWEUKZVOWAVKBJKZHZWK
      WAWLVSVTWAWEULWKABUMKZWLWKWNWCIZWKVTWEWOVSVTWAWEUNVSWBWEUOVTWEWOVTWCWDVTW
      CUPUQURQWKARDZBRDZWNWONVSWBWPWEVJWPVRASUSTVSWBWQWEVRWQVJBSUTTZABVBQVCVSWB
      WNWLNWEABVATUGMWKWQVKRDZVOWMNWRVSWBWSWEVJWSVRVJWIWSAVDVKSVEUSTBVKVFQVCPVG
      VHVI $.

    $( [6-Sep-2014] $)
    elfz-induct $p |- ( A e. NN0 -> ( ( 1 ... A ) u. { ( A + 1 ) } ) =
        ( 1 ... ( A + 1 ) ) ) $=
      ( va cn0 wcel c1 cfz co caddc csn cun fzssp1 cn nn0p1nn cle wbr fznn nnre
      id1 cr syl leid mpbir2and snssd unssd cv wral wss wa wceq nn0z elfz-lastp
      wo cz sylan ssun2 elsn biimpri sseldi elun1 ralrimiva dfss3 sylibr eqssd
      jaoi ) ACDZEAFGZAEHGZIZJZEVGFGZVEVFVHVJEACKVEVGVJVEVGLDZVGVJDZAMVKVLVKVGV
      GNOZVGVGPVKRVKVGSDVMVGQVGUATUBTUCUDVEBUEZVIDZBVJUFVJVIUGVEVOBVJVEVNVJDZUH
      VNVGUIZVNVFDZULZVOVEAUMDVPVSAUJAVNUKUNVQVOVRVQVHVIVNVHVFUOVNVHDVQBVGUPUQU
      RVNVFVHUSVDTUTBVJVIVAVBVC $.
      $( [7-Sep-2014] $)

    $( Can remove the last element of a sequence $)
    ${
      mapfz-rmlast.1 $e |- C e. _V $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      mapfz-rmlast $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) ->
        ( B |` ( 1 ... A ) ) e. ( C ^m ( 1 ... A ) ) ) $=
        ( cn0 wcel c1 caddc co cfz cmap cres wf wss wi fzssp1 fssres ovex elmap
        expcom syl 3imtr4g imp ) AEFZBCGAGHIZJIZKIFZBGAJIZLZCUHKIFZUDUFCBMZUHCU
        IMZUGUJUDUHUFNZUKULOGAEPUKUMULUFCUHBQTUACUFBDGUEJRSCUHUIDGAJRSUBUC $.

      $( [6-Sep-2014] $)
      mapfzres $p |- ( ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) /\
        D e. ( C ^m ( 1 ... B ) ) ) ->
        ( D |` ( 1 ... A ) ) e. ( C ^m ( 1 ... A ) ) ) $=
        ( cn0 wcel cle wbr w3a c1 cfz co cmap wf cz nn0z adantr ovex elmap cres
        wa wss simpr cuz cfv 3ad2ant1 3ad2ant2 simpl3 eluz2 syl3anbrc fzss2 syl
        fssres syl2anc ex 3imtr4g imp ) AFGZBFGZABHIZJZDCKBLMZNMGZDKALMZUAZCVEN
        MGZVBVCCDOZVECVFOZVDVGVBVHVIVBVHUBZVHVEVCUCZVIVBVHUDVJBAUEUFGZVKVJAPGZB
        PGZVAVLVBVMVHUSUTVMVAAQUGRVBVNVHUTUSVNVABQUHRUSUTVAVHUIABUJUKAKBULUMVCC
        VEDUNUOUPCVCDEKBLSTCVEVFEKALSTUQUR $.

      $( [7-Sep-2014] $)
      mapfzconsex $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) /\ D e. C )
          ->
        ( B u. { <. ( A + 1 ) , D >. } ) e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) $=
        ( cn0 wcel c1 cfz co cmap caddc csn cun wf wceq ovex elmap cvv a1i eqid
        w3a cop cin c0 simp2 sylib wss simp3 fsng syl2anc mpbiri snssd fzp1disj
        wb fss 3ad2ant1 fun syl21anc elfz-induct unidm feq23d mpbid sylibr ) AF
        GZBCHAIJZKJGZDCGZUBZHAHLJZIJZCBVJDUCMZNZOZVMCVKKJGVIVFVJMZNZCCNZVMOZVNV
        IVFCBOZVOCVLOZVFVOUDUEPZVRVIVGVSVEVGVHUFCVFBEHAIQRUGVIVODMZVLOZWBCUHVTV
        IWCVLVLPZVLUAVIVJSGZVHWCWDUOWEVIAHLQTVEVGVHUIZVJDSCVLUJUKULVIDCWFUMVOWB
        CVLUPUKVEVGWAVHHAFUNUQVFVOCCBVLURUSVIVPVQVKCVMVEVGVPVKPVHAUTUQVQCPVICVA
        TVBVCCVKVMEHVJIQRVD $.

      $( [7-Sep-2014] $)
      mapfzrecons $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) ->
        B = ( ( B |` ( 1 ... A ) ) u. { <. ( A + 1 ) , ( B ` ( A + 1 ) ) >.
        } ) ) $=
        ( c1 caddc co cfz cmap wcel cn0 wf cres cfv cop csn cun wceq ovex a1i
        wa wfn ffn adantl fnresdm syl elfz-induct adantr eqcomd reseq2d resundi
        elmap eqtr3d ssun2 sseldi eleqtrd fnressn syl2anc uneq2d 3eqtrd sylan2b
        snid ) BCEAEFGZHGZIGJAKJZVDCBLZBBEAHGZMZVCVCBNOPZQZRCVDBDEVCHSULVEVFUAZ
        BBVGVCPZQZMZVHBVLMZQZVJVKBVDMZBVNVKBVDUBZVQBRVFVRVEVDCBUCUDZVDBUEUFVKVD
        VMBVKVMVDVEVMVDRVFAUGUHZUIUJUMVNVPRVKBVGVLUKTVKVOVIVHVKVRVCVDJVOVIRVSVK
        VCVMVDVKVLVMVCVLVGUNVCVLJVKVCAEFSVBTUOVTUPVDVCBUQURUSUTVA $.
        $( [7-Sep-2014] $)

      $( TODO: make a range singleton extraction lemma and redo this on top of
         fvsnun[12] $)
      mapfzconsval $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) /\ D e. C )
          ->
        ( E e. ( 1 ... ( A + 1 ) ) -> ( ( E e. ( 1 ... A ) /\ ( ( B u.
        { <. ( A + 1 ) , D >. } ) ` E ) = ( B ` E ) ) \/ ( E = ( A + 1 ) /\
        ( ( B u. { <. ( A + 1 ) , D >. } ) ` E ) = D ) ) ) ) $=
        ( c1 co wceq wcel cfz cfv wa c0 3ad2ant2 a1i eqtrd wn syl syl2anc caddc
        cn0 cmap w3a cop csn cun wo wi simp1 eqcomd wfun cdm wf ovex elmap ffun
        cin sylbi funsn simp22 biimpi fdm 3syl dmsnop ineq12d fzp1disj 3ad2ant1
        fvun syl21anc cle wbr clt cr nn0re ltp1 wb peano2re ltnle mpbid intnand
        cz nn0z peano2zdi 1z elfz syl3anc mtbird eleq1d mtbid eleq2d fveq2d cvv
        ndmfv fvsng uneq12d 0ss ssid unssi ssun2 eqssi jca olcd 3exp elfz-lastp
        simp23 simp3 eqimss2 eqimss eqssd con3i adantr simpr ord mpd wne sylibr
        df-ne fvunsn orcd pm2.61i ) AGUAHZEIZAUBJZBCGAKHZUCHJZDCJZUDZEGYBKHJZEY
        EJZEBYBDUEUFZUGLZEBLZIZMZEYBIZYLDIZMZUHZUIUIYCYHYIYSYCYHYIUDZYRYOYTYPYQ
        YTYBEYCYHYIUJZUKZYTYLYMEYKLZUGZDYTBULZYKULZBUMZYKUMZURZNIYLUUDIYHYCUUEY
        IYFYDUUEYGYFYECBUNZUUECYEBFGAKUOUPZYECBUQUSOOUUFYTYBDAGUAUOZUTPYTUUIYEY
        BUFZURZNYTUUGYEUUHUUMYTYFUUJUUGYEIZYCYDYFYGYIVAYFUUJUUKVBYECBVCZVDUUHUU
        MIYTYBDVEPVFYHYCUUNNIZYIYDYFUUQYGGAUBVGVHOQEBYKVIVJYTUUDNDUGZDYTYMNUUCD
        YTEUUGJZRYMNIYTYJUUSYTYBYEJZYJYHYCUUTRZYIYDYFUVAYGYDUUTGYBVKVLZYBAVKVLZ
        MZYDUVCUVBYDAYBVMVLZUVCRZYDAVNJZUVEAVOZAVPSYDUVGYBVNJZUVEUVFVQUVHYDUVGU
        VIUVHAVRSAYBVSTVTWAYDYBWBJGWBJZAWBJZUUTUVDVQYDAAWCZWDUVJYDWEPUVLYBGAWFW
        GWHVHOYTYBEYEUUAWIWJYTYEUUGEYTUUGYEYHYCUUOYIYFYDUUOYGYFUUJUUOUUKUUPUSOO
        UKWKWJEBWNSYTUUCYBYKLZDYTEYBYKUUBWLYTYBWMJZYGUVMDIUVNYTUULPYCYDYFYGYIXF
        YBDWMCWOTQWPUURDIYTUURDNDDDWQDWRWSDNWTXAPQQXBXCXDYCRZYHYIYSUVOYHYIUDZYO
        YRUVPYJYNUVPUVOYPYJUHZYJUVOYHYIUJZUVPUVKYIUVQYHUVOUVKYIYDYFUVKYGUVLVHOU
        VOYHYIXGAEXETUVOUVQMZYPRZYJUVOUVTUVQYPYCYPYBEYBEXHEYBXIXJXKXLUVSYPYJUVO
        UVQXMXNXOTUVPYBEXPZYNUVPUVOUWAUVRYBEXRXQBYBDEXSSXBXTXDYA $.
        $( [7-Sep-2014] $)

      ${
        $d c d e f g h i j ph $.
        mapfzinde.10 $e |- [ 0 / a ] [ (/) / b ] ph $.
        mapfzinde.11 $e |- ( ( c e. NN0 /\ d e. ( C ^m ( 1 ... c ) ) /\ e e. C
            ) -> ( [ c / a ] [ d / b ] ph -> [ ( c + 1 ) / a ] [ ( d u. { <. (
            c + 1 ) , e >. } ) / b ] ph ) ) $.
        $( PLEASE PUT DESCRIPTION HERE. $)
        mapfzinde.base $p |- A. f e. ( C ^m ( 1 ... 0 ) ) [ 0 / a ] [ f / b ]
            ph $=
          ( cc0 wsbc co cmap wcel c0 wceq cvv c1o wsb c1 cfz cv wb oveq2i map0e
          fz10 eqtri eleq2i biimpi el1o eqimss2 eqimss eqssd 3syl cc 0cn dfsbcq
          elexi sbcbidv sylancl mpbii rgen ) AFDUAZELMZDBUBLUCNZONZDUDZVHPZAFQM
          ZELMZVFJVJQVIRZLSPVLVFUEVJVITPZVIQRZVMVJVNVHTVIVHBQONTVGQBOUHUFBIUGUI
          UJUKVNVOVIULUKVOQVIQVIUMVIQUNUOUPLUQURUTVMVKVEELSAFQVIUSVAVBVCVD $.

        $( [7-Sep-2014] $)
        mapfzinde.ind $p |- ( g e. NN0 -> ( A. f e. ( C ^m ( 1 ... g ) ) [ g /
            a ]
        [ f / b ] ph -> A. f e. ( C ^m ( 1 ... ( g + 1 ) ) ) [ ( g + 1 ) / a ]
        [ f / b ] ph ) ) $=
          ( vh wcel wsb c1 co wsbc wa wb cv cn0 cfz cmap wral cres mapfz-rmlast
          caddc adantlr simplr cvv vex dfsbcq sbcbidv mpan2 rcla4va syl2anc cfv
          wceq cop csn cun simplll jca wf elmap biimpi cn cle wbr nn0p1nn nn0re
          ovex cr peano2re leid 3syl syl mpbird ffvelrn syl2anr anim1i wi resex
          fznn weq w3a simp1 eleq1d simp2 oveq2d eleq12d anbi12d simp3 3ad2ant1
          bitrd oveq1 oveq1d opeq12d sneqd uneq12d imbi12d simpll simprl simprr
          fvex 3jca sylc vtocl3 mapfzrecons mpdan ralrimiva cbvralv sylib ex )
          EUAZUBNZAGDOZFEOZDBPXPUCQZUDQZUEZXRFXPPUHQZRZDBPYCUCQZUDQZUEZXQYBSZAG
          MOZFYCRZMYFUEYGYHYJMYFYHMUAZYFNZSZAGYKXTUFZRZFEOZYJYMYNYANZYBYPXQYLYQ
          YBXPYKBJUGZUIXQYBYLUJXSYPDYNYADUAZYNUSZXPUKNZXSYPTEULZYTXRYOFXPUKAGYS
          YNUMUNUOUPUQYMYPSZYJAGYNYCYCYKURZUTZVAZVBZRZFYCRZUUCXQYQSZUUDBNZYPSZU
          UIUUCXQYQXQYBYLYPVCZUUCXQYLYQUUMYHYLYPUJZYRUQVDYMUUKYPXQYLUUKYBYLYEBY
          KVEZYCYENZUUKXQYLUUOBYEYKJPYCUCVMVFVGXQUUPYCVHNZYCYCVIVJZSZXQUUQUURXP
          VKZXQXPVNNYCVNNUURXPVLXPVOYCVPVQVDXQUUQUUPUUSTUUTYCYCWEVRVSYEBYCYKVTW
          AUIWBHUAZUBNZIUAZBPUVAUCQZUDQZNZSZCUAZBNZAGIOZFHOZSZSZAGUVCUVAPUHQZUV
          HUTZVAZVBZRZFUVNRZWCUUJUULSZUUIWCHICXPYNUUDUUBYKXTMULWDYCYKXFHEWFZUVC
          YNUSZUVHUUDUSZWGZUVMUVTUVSUUIUWDUVGUUJUVLUULUWDUVBXQUVFYQUWDUVAXPUBUW
          AUWBUWCWHZWIUWDUVCYNUVEYAUWAUWBUWCWJZUWDUVDXTBUDUWDUVAXPPUCUWEWKWKWLW
          MUWDUVIUUKUVKYPUWDUVHUUDBUWAUWBUWCWNZWIUWDUVKUVJFEOZYPUWAUWBUVKUWHTUW
          CUVJFUVAXPUMWOUWDUUAUWHYPTUUBUWDUVJYOFXPUKUWDUWBUVJYOTUWFAGUVCYNUMVRU
          NUOWPWMWMUWDUVSUVRFYCRZUUIUWDUVNYCUSZUVSUWITUWAUWBUWJUWCUVAXPPUHWQWOU
          VRFUVNYCUMVRUWDYCUKNZUWIUUITXPPUHVMZUWDUVRUUHFYCUKUWDUVQUUGUSUVRUUHTU
          WDUVCYNUVPUUFUWFUWDUVOUUEUWDUVNYCUVHUUDUWDUVAXPPUHUWEWRUWGWSWTXAAGUVQ
          UUGUMVRUNUOWPXBUVMUVBUVFUVIWGUVKUVSUVMUVBUVFUVIUVBUVFUVLXCUVBUVFUVLUJ
          UVGUVIUVKXDXGUVGUVIUVKXELXHXIUQUUCXQYLYJUUITZUUMUUNXQYLSZUWKUWMUWLUWN
          YIUUHFYCUKUWNYKUUGUSYIUUHTXPYKBJXJAGYKUUGUMVRUNUOUQVSXKXLYJYDMDYFMDWF
          ZUWKYJYDTUWLUWOYIXRFYCUKAGYKYSUMUNUOXMXNXO $.

        $( [7-Sep-2014] $)
        mapfzinde $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> [ A / a
            ] [ B / b ] ph ) $=
          ( vh vg c1 cfz co cmap wsbc wral vf cn0 wcel wa wsb cv cc0 caddc wceq
          eqidd oveq2 oveq123d dfsbcq raleqbidv weq oveq2d mapfzinde.ind nn0ind
          mapfzinde.base adantr simpll simplr jca simpr sbcbidv syl2anc rcla4dv
          wb simpl imp ex mpd ) BUBUCZCDOBPQZRQZUCZUDZAGMUEZFBSZMVOTZAGCSZFBSZV
          MVTVPVRFUAUEZMDOUAUFZPQZRQZTVRFUGSZMDOUGPQZRQZTVRFNUEZMDONUFZPQZRQZTV
          RFWKOUHQZSZMDOWNPQZRQZTVTUANBWDUGUIZWCWGMWFWIWRDDWEWHRRWRRUJWRDUJWDUG
          OPUKULVRFWDUGUMUNUANUOZWCWJMWFWMWSDDWEWLRRWSRUJWSDUJWDWKOPUKULVRFWDWK
          UMUNWDWNUIZWCWOMWFWQWTWEWPDRWDWNOPUKUPVRFWDWNUMUNWDBUIZWCVSMWFVOXAWEV
          NDRWDBOPUKUPVRFWDBUMUNADEMFGHIJKLUSADEMNFGHIJKLUQURUTVQVTWBVQVTUDZVQV
          TWBXBVMVPVMVPVTVAVMVPVTVBVCVQVTVDVQVTWBVMVSWBMCVOVMMUFZCUIZUDXDVMVSWB
          VHVMXDVDVMXDVIXDVRWAFBUBAGXCCUMVEVFVGVJVFVKVL $.
          $( [7-Sep-2014] $)
      $}

      ${
        $d f g h i a b c d e A $.  $d f g h i a b c d e B $.
        $d f g h i c d e ph $.  $d f g h i a b ps $.  $d f g h i a b ch $.
        $d f g h i a b th $.  $d f g h i a b ta $.
        mapfzind.2 $e |- ( ( a = A /\ b = B ) -> ( ph <-> ps ) ) $.
        mapfzind.4 $e |- ( ( a = 0 /\ b = (/) ) -> ( ph <-> ch ) ) $.
        mapfzind.6 $e |- ( ( a = c /\ b = d ) -> ( ph <-> th ) ) $.
        mapfzind.8 $e |- ( ( a = ( c + 1 ) /\ b = ( d u. { <. ( c + 1 ) , e >.
        } ) ) -> ( ph <-> ta ) ) $.
        mapfzind.10 $e |- ch $.
        mapfzind.11 $e |- ( ( c e. NN0 /\ d e. ( C ^m ( 1 ... c ) ) /\ e e. C )
            -> ( th -> ta ) ) $.
        $( PLEASE PUT DESCRIPTION HERE. $)
        mapfzind $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> ps ) $=
          ( cn0 wcel c1 cfz co cmap wa wsbc c0 cc0 cc 0cn elexi sbc2ie mpbir cv
          0ex w3a wsb cop csn cun vex ovex snex unex 3imtr4g mapfzinde sbc2iegf
          caddc ax-17 mpbid ) FUAUBGHUCFUDUEUFUEZUBZUGAKGUHJFUHBAFGHIJKLMNAKUIU
          HJUJUHCSACJKUJUIUJUKULUMUQPUNUOLUPZUAUBMUPZHUCVOUDUEUFUEUBIUPZHUBURDE
          AKMUSJLUSAKVPVOUCVJUEZVQUTZVAZVBZUHJVRUHTADJKVOVPLVCMVCZQUNAEJKVRWAVO
          UCVJVDVPVTWBVSVEVFRUNVGVHABJKFGUAVMBJVKBKVKVNJVKOVIVL $.
          $( [7-Sep-2014] $)
      $}
      $( PLEASE PUT DESCRIPTION HERE. $)
      mapssi $p |- ( ( A C_ B /\ B e. _V ) -> ( A ^m C ) C_ ( B ^m C ) ) $=
        ( va cvv wcel wss cmap co wa cv wf cab fss wceq ancoms mapvalg sylancl
        wi expcom adantl ss2abdv ssexg simpl 3sstr4d ) BFGZABHZACIJZBCIJZHUGUHK
        ZCAELZMZENZCBULMZENZUIUJUKUMUOEUHUMUOTUGUMUHUOCABULOUAUBUCUKAFGZCFGZUIU
        NPUHUGUQABFUDQDACFFERSUKUGURUJUPPUGUHUEDBCFFERSUFQ $.
        $( [6-Sep-2014] $)
    $}

    ${
      mapcan0.0 $e |- B e. _V $.
      mapcan0.1 $e |- C e. _V $.
      mapcan0.2 $e |- D e. _V $.
      mapcan0.3 $e |- E e. _V $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      mapcan0 $p |- ( ( A e. ( B ^m C ) /\ A e. ( D ^m E ) ) -> C = E ) $=
        ( cmap co wcel wa cdm wceq wf elmap biimpi fdm syl adantr adantl eqtr3d
        ) ABCJKLZADEJKLZMANZCEUDUFCOZUEUDCBAPZUGUDUHBCAFGQRCBASTUAUEUFEOZUDUEED
        APZUIUEUJDEAHIQREDASTUBUC $.
        $( [4-Sep-2014] $)
    $}

    ${
      mapcan1.0 $e |- A e. B $.
      mapcan1.1 $e |- C e. _V $.
      mapcan1.2 $e |- D e. _V $.
      mapcan1.3 $e |- B e. _V $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      mapcan1 $p |- ( ( B ^m C ) = ( B ^m D ) -> C = D ) $=
        ( csn cxp cmap co wcel wceq elexi constmap ax-mp wa simpl simpr eleqtrd
        mapcan0 syldan mpan ) CAIJZBCKLZMZUFBDKLZNZCDNZABMUGECABFABEOHPQUGUIUEU
        HMUJUGUIRUEUFUHUGUISUGUITUAUEBCBDHFHGUBUCUD $.
        $( [4-Sep-2014] $)
    $}

    ${
      mapco1.1 $e |- C e. _V $.
      mapco1.2 $e |- A e. _V $.
      ${
        mapco1.3 $e |- E e. _V $.
        $( PLEASE PUT DESCRIPTION HERE. $)
        mapco1 $p |- ( ( B e. ( C ^m A ) /\ D : C --> E ) ->
        ( D o. B ) e. ( E ^m A ) ) $=
          ( cmap co wcel wf wa ccom simpr elmap biimpi adantr fco syl2anc
          sylibr ) BCAIJKZCEDLZMZAEDBNZLZUEEAIJKUDUCACBLZUFUBUCOUBUGUCUBUGCABFG
          PQRACEDBSTEAUEHGPUA $.
          $( [7-Sep-2014] $)
      $}
      $( PLEASE PUT DESCRIPTION HERE. $)
      mapfun $p |- ( B e. ( A ^m C ) -> Fun B ) $=
        ( cmap co wcel wf wfun elmap ffun sylbi ) BACFGHCABIBJACBEDKCABLM $.

      $( [7-Sep-2014] $)
      elmapdm $p |- ( B e. ( A ^m C ) -> dom B = C ) $=
        ( cmap co wcel wf cdm wceq elmap fdm sylbi ) BACFGHCABIBJCKACBEDLCABMN
        $.

      $( [7-Sep-2014] $)
      mapfv $p |- ( ( B e. ( A ^m C ) /\ D e. C ) -> ( B ` D ) e. A ) $=
        ( cmap co wcel wf cfv elmap ffvelrn sylanb ) BACGHICABJDCIDBKAIACBFELCA
        DBMN $.
        $( [7-Sep-2014] $)
      ${
        $d u B $.  $d u C $.  $d u D $.
        mapdmres.3 $e |- D e. _V $.
        $( PLEASE PUT DESCRIPTION HERE. $)
        mapdmres $p |- ( ( B e. ( A ^m C ) /\ A. u e. C ( B ` u ) e. D ) ->
        B e. ( D ^m C ) ) $=
          ( cmap co wcel cv cfv wral wa wf wfn crn wss elmap ffn sylbi fnfvrnss
          adantr sylan df-f sylanbrc sylibr ) CBDIJKZALCMEKADNZOZDECPZCEDIJKUKC
          DQZCRESZULUIUMUJUIDBCPUMBDCGFTDBCUAUBZUDUIUMUJUNUOADECUCUEDECUFUGEDCH
          FTUH $.
          $( [7-Sep-2014] $)
      $}
    $}

    ${
      elmapfz.0 $e |- C e. _V $.
      $( PLEASE PUT DESCRIPTION HERE. $)
      elmapfz0 $p |- (/) e. ( C ^m ( 1 ... 0 ) ) $=
        ( c0 c1o c1 cc0 cfz co cmap 0lt1o fz10 oveq2i map0e eqtri eleqtrri ) CD
        AEFGHZIHZJQACIHDPCAIKLABMNO $.

      $( [9-Sep-2014] $)
      elmapfz1 $p |- ( A e. C -> { <. 1 , A >. } e. ( C ^m ( 1 ... 1 ) ) ) $=
        ( wcel c1 cfz co cop csn wf cmap wss cz wa wceq 1z eqidd syl2anc sylibr
        jctl fsng biimpar snssi fss fzsn ax-mp feq2i ovex elmap ) ABDZEEFGZBEAH
        IZJZULBUKKGDUJEIZBULJZUMUJUNAIZULJZUPBLUOUJEMDZUJNZULULOZUQUJURPTUJULQU
        SUQUTEAMBULUAUBRABUCUNUPBULUDRUKUNBULURUKUNOPEUEUFUGSBUKULCEEFUHUIS $.
        $( [9-Sep-2014] $)
      ${
        $d x C $.
        $( PLEASE PUT DESCRIPTION HERE. $)
        elmapeliunmap $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> B e.
            U_ x e. NN0 ( C ^m ( 1 ... x ) ) ) $=
          ( va cn0 wcel c1 cfz co cmap wa cv ciun wrex wceq oveq2 oveq2d eleq2d
          rcla4ev eliun sylibr weq cbviunv syl6eleq ) BGHCDIBJKZLKZHZMZCFGDIFNZ
          JKZLKZOZAGDIANZJKZLKZOUJCUMHZFGPCUNHURUIFBGUKBQZUMUHCUSULUGDLUKBIJRST
          UAFCGUMUBUCFAGUMUQFAUDULUPDLUKUOIJRSUEUF $.
          $( [9-Sep-2014] $)
      $}
    $}
  $}

$( Note for future: a-i are dummy variables that are disjoint from each other
   and from all other variables.  they should not be used in the statement of
   a theorem. $)


$( loosely inspired by some lecture notes I found by Lou van den Dries $)
  $c RecZer RecSuc RecSub RecSea RecPrj RecPrc RecParF RecArity RecParFa
      RecTotF RecTotFa RecArithPrimitiveStep RecArithGeneralStep
      RecArithPrimitiveL RecArithPrimitive RecArithGeneralL RecArithGeneral
      RecPrimitive RecGeneral RecPreList $.
  ${
    $( PLEASE PUT DESCRIPTION HERE. $)
    creczer $a class RecZer $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecsuc $a class RecSuc $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecprj $a class RecPrj $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecsub $a class RecSub $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecsea $a class RecSea $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecprc $a class RecPrc $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecparf $a class RecParF $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarity $a class RecArity $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecparfa $a class RecParFa $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crectotf $a class RecTotF $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crectotfa $a class RecTotFa $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecprelist $a class RecPreList $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithprimitivestep $a class RecArithPrimitiveStep $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithprimitivel $a class RecArithPrimitiveL $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithprimitive $a class RecArithPrimitive $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecprimitive $a class RecPrimitive $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithgeneralstep $a class RecArithGeneralStep $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithgenerall $a class RecArithGeneralL $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecarithgeneral $a class RecArithGeneral $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    crecgeneral $a class RecGeneral $.

    $d x y z f g h w a b c i j k $.

    $( -- unified treatment of partial/total functions for recursion theory -- $)

    $( Set of partial functions from NN^x -> NN, not necessarily recursive.
       Set theoretically these are total functions, in order to avoid a
       pathology where nowhere-defined functions can have multiple arities at
       the same time. $)
    df-recparfa $a |- RecParFa = ( x e. NN0 |-> ( ( NN0 u. { ( Undef ` NN0 ) }
        ) ^m ( NN0 ^m ( 1 ... x ) ) ) ) $.

    $( All partial functions, regardless of arity. $)
    df-recparf $a |- RecParF = U. ran RecParFa $.

    $( Arity of a partial function. $)
    df-recarity $a |- RecArity = ( f e. RecParF |-> ( iota_ x e. NN0 f e. (
        RecParFa ` x ) ) ) $.

    $( Total functions, a subset of partial functions. $)
    df-rectotfa $a |- RecTotFa = ( x e. NN0 |-> ( NN0 ^m ( NN0 ^m ( 1 ... x ) )
        ) ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-rectotf $a |- RecTotF = U. ran RecTotFa $.
    $( we can use the same arity $)

    $( TODO: define RecPreList $)

    $( -- recursive function builders -- $)

    $( Zero recursive function. $)
    df-reczer $a |- RecZer = ( x e. ( NN0 ^m ( 1 ... 0 ) ) |-> 0 ) $.
    $( Successor. $)
    df-recsuc $a |- RecSuc = ( x e. ( NN0 ^m ( 1 ... 1 ) ) |-> ( ( x ` 1 ) + 1
        ) ) $.
    $( Projector family: not defined for zero arity. $)
    df-recprj $a |- RecPrj = ( x e. NN , y e. NN |-> ( z e. ( NN0 ^m ( 1 ... y
        ) ) |-> if ( x <_ y , ( z ` x ) , 0 ) ) ) $.
    $( Substitution. $)
    df-recsub $a |- RecSub =
        ( x e. NN0 , y e. NN0 |->
            ( f e. ( RecParFa ` x ) , g e. ( ( RecParFa ` y ) ^m ( 1 ... x ) )
        |->
                ( h e. ( NN ^m ( 1 ... y ) ) |->
                    if (
                        E. z e. ( 1 ... x ) ( ( g ` z ) ` h ) = ( Undef ` NN0 )
        ,
                        ( Undef ` NN0 ) ,
                        ( f ` ( w e. ( 1 ... x ) |-> ( ( g ` w ) ` h ) ) )
                    )
                )
            )
        ) $.

    $( Primitive recursion. $)
    df-recprc $a |- RecPrc = ( x e. NN0 |->
        ( g e. ( RecParFa ` x ) , h e. ( RecParFa ` ( x + 1 ) ) |->
            ( y e. ( 1 ... ( x + 1 ) ) |->
                ( seq 0 (
                    ( w e. ( NN0 u. { ( Undef ` NN0 ) } ) , a e. ( NN0 u. { (
        Undef ` NN0 ) } ) |->
                        if ( w = ( Undef ` NN0 ) , ( Undef ` NN0 ) ,
                            ( h ` ( ( y |` ( 1 ... x ) ) u. { <. ( x + 1 ) , w
        >. } ) )
                        )
                    ) ,
                    ( NN0 X. { g ` ( y |` ( 1 ... x ) ) } )
                ) ` ( y ` ( x + 1 ) ) )
            )
        )
    ) $.

    $( Unbounded search / general recursion.  Here originates Undef. $)
    df-recsea $a |- RecSea = ( x e. NN0 |->
        ( f e. ( RecParFa ` ( x + 1 ) ) |->
            ( y e. ( 1 ... x ) |->
                ( iota_ z e. NN0 (
                    ( f ` ( y u. { <. ( x + 1 ) , z >. } ) ) = 0 /\
                    A. w e. NN0 ( w < z -> ( f ` ( y u. { <. ( x + 1 ) , z >. }
        ) ) e. ( NN0 \ { 0 } ) )
                ) )
            )
        )
    ) $.

    $( -- let's define the arithmetization predicate and the set of general recursive functions at the same time, I think this will save work -- $)

    $( naming a step of the construction, do not use except to prove properties
       on RecArithPrimitiveL $)
    df-recarithprimitivestep $a |- RecArithPrimitiveStep = ( f e. ~P ( NN0 X.
        RecParF ) |-> { <. x , g >. |
        (
            ( ( x = ( 1 ,n 0 ) /\ g = RecZer ) \/
                ( x = ( 1 ,n 1 ) /\ g = RecSuc ) ) \/
            (
                E. i e. NN E. j e. NN ( x = ( 2 ,n ( i ,n j ) ) /\ i <_ j /\ g
        = ( i RecPrj j ) ) \/
                E. i e. NN E. j e. NN E. a e. ( RecParFa ` i ) E. b e. ( (
        RecParFa ` j ) ^m ( 1 ... i ) )
                    E. c e. NN0 E. d e. NN0 E. e e. ( NN0 ^m ( 1 ... i ) )
                        ( ( c f a /\ A. l e. ( 1 ... i ) ( e ` l ) f ( b ` l )
        ) /\
                            ( x = ( 3 ,n ( i ,n ( c ,n d ) ) ) /\ d = (
        RecPreList ` e ) /\ g = ( a ( i RecSub j ) b ) ) ) \/
                E. i e. NN E. j e. NN0 E. k e. NN0 E. a e. ( RecParFa ` i ) E.
        b e. ( RecParFa ` ( i + 1 ) )
                    ( ( j f a /\ k f b ) /\ ( x = ( 4 ,n ( j ,n k ) ) /\ g = (
        a ( RecPrc ` i ) b ) ) )
            )
        )
    } ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recarithgeneralstep $a |- RecArithGeneralStep ( f e. ~P ( NN0 X. RecParF
        ) |-> { <. x , g >. |
        x ( RecArithPrimitiveStep ` f ) g \/
        E. i e. NN E. j e. NN0 E. a e. ( RecParFa ` ( i + 1 ) )
            ( j f a /\ x = ( 5 ,n j ) /\ g = ( ( RecSea ` i ) ` a ) )
    } ) $.

    $( Primitive recursion - levelled version, avoid using. $)
    df-recarithprimitivel $a |- RecArithPrimitiveL = rec (
        RecArithPrimitiveStep , (/) ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recarithgenerall $a |- RecArithGeneralL = rec ( RecArithGeneralStep ,
        (/) ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recarithprimitive $a |- RecArithPrimitive = ( RecArithPrimitiveL ` om )
        $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recarithgeneral $a |- RecArithGeneral = ( RecArithGeneralL ` om ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recprimitive $a |- RecPrimitive = ran RecArithPrimitive $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    df-recgeneral $a |- RecGeneral = ran RecArithGeneral $.
  $}

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    dfrecparfa1 $p |- ( A e. NN0 -> ( RecParFa ` A ) = ( ( NN0 u. { ( Undef `
        NN0 ) } ) ^m ( NN0 ^m ( 1 ... A ) ) ) ) $=
      ( va cn0 cund cfv csn cun c1 cv cfz cmap crecparfa wceq oveq2 df-recparfa
      co oveq2d ovex fvmpt ) BACCDEFGZCHBIZJPZKPZKPTCHAJPZKPZKPCLUAAMZUCUETKUFU
      BUDCKUAAHJNQQBOTUEKRS $.

    $( [4-Sep-2014] $)
    dfrectotfa1 $p |- ( A e. NN0 -> ( RecTotFa ` A ) = ( NN0 ^m ( NN0 ^m ( 1
        ... A ) ) ) ) $=
      ( va cn0 c1 cv co cmap crectotfa wceq oveq2 oveq2d df-rectotfa ovex fvmpt
      cfz ) BACCDBEZOFZGFZGFCCDAOFZGFZGFCHPAIZRTCGUAQSCGPADOJKKBLCTGMN $.

    $( [4-Sep-2014] $)
    totfa-is-parfa $p |- ( A e. NN0 -> ( RecTotFa ` A ) C_ ( RecParFa ` A ) )
        $=
      ( cn0 wcel crectotfa cfv cund csn cun c1 cfz co crecparfa dfrectotfa1 wss
      cmap ssun1 a1i nn0ex snex unex ovex mapss eqsstrd dfrecparfa1 sseqtr4d
      syl ) ABCZADEZBBFEZGZHZBIAJKZOKZOKZALEUGUHBUMOKZUNAMUGBUKNZUOUNNUPUGBUJPQ
      BUKUMBUJRUISTBULOUAUBUFUCAUDUE $.

    $( [4-Sep-2014] $)
    totfa-fn $p |- RecTotFa Fn NN0 $=
      ( va cn0 c1 cv cfz cmap cvv wcel crectotfa wfn df-rectotfa fnmpt ovex a1i
      co mprg ) BBCADZEOFOZFOZGHZIBJABABSIGAKLTQBHBRFMNP $.

    $( [4-Sep-2014] $)
    parfa-fn $p |- RecParFa Fn NN0 $=
      ( va cn0 cund cfv csn cun c1 cv cfz co cmap cvv crecparfa wfn df-recparfa
      wcel fnmpt ovex a1i mprg ) BBCDEFZBGAHZIJKJZKJZLPZMBNABABUDMLAOQUEUBBPUAU
      CKRST $.

    $( [4-Sep-2014] $)
    dfrectotf1 $p |- RecTotF = U_ a e. NN0 ( RecTotFa ` a ) $=
      ( crectotf crectotfa crn cuni cn0 cv cfv ciun df-rectotf wfn wceq fniunfv
      totfa-fn ax-mp eqtr4i ) BCDEZAFAGCHIZJCFKRQLNAFCMOP $.

    $( [4-Sep-2014] $)
    dfrecparf1 $p |- RecParF = U_ a e. NN0 ( RecParFa ` a ) $=
      ( crecparf crecparfa crn cuni cn0 cv cfv ciun df-recparf wfn wceq fniunfv
      parfa-fn ax-mp eqtr4i ) BCDEZAFAGCHIZJCFKRQLNAFCMOP $.

    $( [4-Sep-2014] $)
    totf-is-parf $p |- RecTotF C_ RecParF $=
      ( va crectotf cn0 cv crectotfa cfv ciun crecparf dfrectotf1 crecparfa wss
      ss2iun totfa-is-parfa mprg dfrecparf1 sseqtr4i eqsstri ) BACADZEFZGZHAITA
      CRJFZGZHSUAKTUBKACACSUALRMNAOPQ $.
      $( [19-Oct-2014] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    totfa-is-parfa-g $p |- ( RecTotFa ` A ) C_ ( RecParFa ` A ) $=
      ( cn0 wcel crectotfa cfv crecparfa wss totfa-is-parfa wn c0 wceq totfa-fn
      cdm wfn fndm ax-mp eqcomi eleq2i notbii biimpi ndmfv syl 0ss a1i eqsstrd
      pm2.61i ) ABCZADEZAFEZGAHUGIZUHJUIUJADMZCZIZUHJKUJUMUGULBUKAUKBDBNUKBKLBD
      OPQRSTADUAUBJUIGUJUIUCUDUEUF $.
      $( [5-Sep-2014] $)

    $( use fz1eqb, elfvdm. $)
    parfa-domlem $p |- ( A e. ( RecParFa ` B ) -> B e. NN0 ) $=
      ( crecparfa cfv wcel cdm cn0 elfvdm id wceq wfn parfa-fn fndm a1i eleqtrd
      ax-mp syl ) ABCDEBCFZEZBGEABCHSBRGSIRGJZSCGKTLGCMPNOQ $.

    $( [4-Sep-2014] $)
    totfa-domlem $p |- ( A e. ( RecTotFa ` B ) -> B e. NN0 ) $=
      ( crectotfa cfv wcel cdm cn0 elfvdm id wceq wfn totfa-fn fndm a1i eleqtrd
      ax-mp syl ) ABCDEBCFZEZBGEABCHSBRGSIRGJZSCGKTLGCMPNOQ $.
      $( [4-Sep-2014] $)

    $( use elmapg to derive C : (^A) --> NN0 and C : (^B) ---> NN0 $)
    $( use fdm to get (^A) = dom C = (^B) $)
    parfa-disjoint $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. ( RecParFa ` A
        ) /\ C e. ( RecParFa ` B ) ) ) -> A = B ) $=
      ( cn0 wcel wa crecparfa cfv c1 cfz wceq cund csn cmap dfrecparfa1 eleqtrd
      co cun nn0ex ovex simprl ad2antrr ad2antlr jca snex unex mapcan0 cc0 0nn0
      simprr mapcan1 3syl fz1eqb biimpd imp syldan ) ADEZBDEZFZCAGHZEZCBGHZEZFZ
      IAJQZIBJQZKZABKZUSVDFZCDDLHZMZRZDVENQZNQZEZCVLDVFNQZNQZEZFVMVPKVGVIVOVRVI
      CUTVNUSVAVCUAUQUTVNKURVDAOUBPVICVBVQUSVAVCUJURVBVQKUQVDBOUCPUDCVLVMVLVPDV
      KSVJUEUFZDVENTVSDVFNTUGUHDVEVFUIIAJTIBJTSUKULUSVGVHUSVGVHABUMUNUOUP $.

    $( [4-Sep-2014] $)
    parfa-disjoint-g $p |- ( ( C e. ( RecParFa ` A ) /\ C e. ( RecParFa ` B ) )
        -> A = B ) $=
      ( cn0 wcel crecparfa cfv wceq parfa-domlem anim12i parfa-disjoint mpancom
      wa ) ADEZBDEZMCAFGEZCBFGEZMABHPNQOCAICBIJABCKL $.

    $( [5-Sep-2014] $)
    dfarity1 $p |- ( A e. RecParF -> ( RecArity ` A ) = ( iota_ a e. NN0 A e. (
        RecParFa ` a ) ) ) $=
      ( vb cv crecparfa cfv wcel crio crecparf crecarity wceq eleq1 df-recarity
      cn0 riotabidv riotaex fvmpt ) CACDZBDEFZGZBNHASGZBNHIJRAKTUABNRASLOBCMUAB
      NPQ $.

    $( [4-Sep-2014] $)
    parfa-is-parf $p |- ( A e. NN0 -> ( RecParFa ` A ) C_ RecParF ) $=
      ( va cn0 wcel crecparfa cfv cv ciun crecparf ssiun2s dfrecparf1 syl6sseqr
      fveq2 ) ACDAEFZBCBGZEFZHIBCPANOAEMJBKL $.

    $( [4-Sep-2014] $)
    totfa-is-totf $p |- ( A e. NN0 -> ( RecTotFa ` A ) C_ RecTotF ) $=
      ( va cn0 wcel crectotfa cfv cv ciun crectotf ssiun2s dfrectotf1 syl6sseqr
      fveq2 ) ACDAEFZBCBGZEFZHIBCPANOAEMJBKL $.

    $( [4-Sep-2014] $)
    dfparf2 $p |- ( A e. RecParF <-> E. a e. NN0 A e. ( RecParFa ` a ) ) $=
      ( crecparf wcel cn0 crecparfa cfv ciun wrex dfrecparf1 eleq2i eliun bitri
      cv ) ACDABEBNFGZHZDAODBEICPABJKBAEOLM $.

    $( [5-Sep-2014] $)
    dftotf2 $p |- ( A e. RecTotF <-> E. a e. NN0 A e. ( RecTotFa ` a ) ) $=
      ( crectotf wcel cn0 crectotfa cfv ciun wrex dfrectotf1 eleq2i eliun bitri
      cv ) ACDABEBNFGZHZDAODBEICPABJKBAEOLM $.

    $( [5-Sep-2014] $)
    dfarity4 $p |- ( B e. ( RecParFa ` A ) -> ( RecArity ` B ) = A ) $=
      ( va crecparfa cfv wcel cn0 crecarity wceq parfa-domlem crio crecparf wss
      wa cv parfa-is-parf adantl simpl sseldd simpl1 syl simpr parfa-disjoint-g
      dfarity1 w3a syl2anc fveq2 eqcomd eleqtrd impbida riota5 eqtrd mpdan ) BA
      DEZFZAGFZBHEZAIBAJUOUPNZUQBCOZDEZFZCGKZAURBLFUQVBIURUNLBUPUNLMUOAPQUOUPRS
      BCUDUAUOVACGAUOUPUSGFZUEZVAUSAIZVDVANVAUOVEVDVAUBUOUPVCVATUSABUCUFVDVENBU
      NUTUOUPVCVETVEUNUTIVDVEUTUNUSADUGUHQUIUJUKULUM $.
      $( [5-Sep-2014] $)

    $( possible to factor out "partition of sets"/"rank function" concept. $)
    arity-defined $p |- ( A e. RecParF -> ( RecArity ` A ) e. NN0 ) $=
      ( va crecparf wcel crecparfa cfv cn0 wrex crecarity dfarity4 parfa-domlem
      cv dfparf2 eqeltrd rexlimivw sylbi ) ACDABLZEFDZBGHAIFZGDZABMRTBGRSQGQAJA
      QKNOP $.
      $( [19-Oct-2014] $)
    $( PLEASE PUT DESCRIPTION HERE. $)
    arity-fn $p |- RecArity Fn RecParF $=
      ( va vb cv crecparfa cfv wcel cn0 crio cvv crecparf crecarity wfn riotaex
      wral rgenw df-recarity fnmpt ax-mp ) ACBCDEFZBGHZIFZAJNKJLUAAJSBGMOAJTKIB
      APQR $.

    $( [4-Sep-2014] $)
    arity-fun $p |- RecArity : RecParF --> NN0 $=
      ( va crecparf cn0 crecarity wf wfn wcel wral ffnfv arity-fn arity-defined
      cv cfv rgen mpbir2an ) BCDEDBFALZDMCGZABHABCDIJQABPKNO $.

    $( [4-Sep-2014] $)
    arity-df2 $p |- ( ( A e. NN0 /\ B e. RecParF ) -> ( B e. ( RecParFa ` A )
        <-> ( RecArity ` B ) = A ) ) $=
      ( va vb cn0 wcel crecparf wa crecparfa cfv cv crio wceq crecarity wreu wb
      dfarity1 adantl arity-defined eqeltrrd nn0ex riotaclb sylibr ax-17 eleq2d
      a17d fveq2 riota2f syldan eqeq1d bitr4d ) AEFZBGFZHZBAIJZFZBCKZIJZFZCELZA
      MZBNJZAMULUMUSCEOZUPVAPUNUTEFVCUNVBUTEUMVBUTMULBCQRZUMVBEFULBSRTUSCEUAUBU
      CUSUPCDEADKAFCUDULUPCUFUQAMURUOBUQAIUGUEUHUIUNVBUTAVDUJUK $.

    $( [4-Sep-2014] $)
    arity-df3 $p |- ( B e. ( RecParFa ` A ) <-> ( B e. RecParF /\ ( RecArity `
        B ) = A ) ) $=
      ( crecparfa cfv wcel crecparf crecarity wa cn0 parfa-domlem parfa-is-parf
      wceq wss adantl simpl sseldd mpdan dfarity4 jca simpr wb adantr arity-df2
      arity-defined eqeltrrd syl2anc mpbird impbii ) BACDZEZBFEZBGDZALZHZUJUKUM
      UJAIEZUKBAJUJUOHUIFBUOUIFMUJAKNUJUOOPQABRSUNUJUMUKUMTZUNUOUKUJUMUAUNULAIU
      PUKULIEUMBUDUBUEUKUMOABUCUFUGUH $.

    $( [4-Sep-2014] $)
    arity-dftot $p |- ( B e. ( RecTotFa ` A ) <-> ( B e. RecTotF /\ ( RecArity
        ` B ) = A ) ) $=
      ( vd crectotfa wcel crectotf crecarity wceq wa totfa-domlem totfa-is-totf
      cfv cn0 wss simpl crecparfa crecparf totfa-is-parfa-g sseli simpr 3syl cv
      adantl sseldd arity-df3 biimpi adantr jca totf-is-parf sseldi sylanbrc wi
      mpdan wrex dftotf2 parfa-disjoint-g sylan eleqtrd ex rexlimivw sylbi sylc
      fveq2d impbii ) BADLZEZBFEZBGLAHZIZVFAMEZVIBAJVFVJIZVGVHVKVEFBVJVEFNVFAKU
      CVFVJOUDVFVHVJVFBAPLZEZBQEZVHIZVHVEVLBARSVMVOABUEZUFVNVHTUAUGUHUMVIVGVMVF
      VGVHOZVIVNVHVMVIFQBUIVQUJVGVHTVPUKVGBCUBZDLZEZCMUNVMVFULZBCUOVTWACMVTVMVF
      VTVMIZBVSVEVTVMOWBVRADVTBVRPLZEVMVRAHVSWCBVRRSVRABUPUQVCURUSUTVAVBVD $.
      $( [4-Sep-2014] $)
  $}

  ${
    $d a b c d e f g $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    fun-is-totf $p |- ( ( A e. NN0 /\ B : ( NN0 ^m ( 1 ... A ) ) --> NN0 ) -> B
        e. ( RecTotFa ` A ) ) $=
      ( cn0 wcel c1 cfz co cmap wf wa crectotfa nn0ex ovex elmap biimpri adantl
      cfv wceq dfrectotfa1 adantr eleqtrrd ) ACDZCEAFGZHGZCBIZJBCUDHGZAKQZUEBUF
      DZUBUHUECUDBLCUCHMNOPUBUGUFRUEASTUA $.

    $( [5-Sep-2014] $)
    compactified-nn-ex $p |- ( NN0 u. { ( Undef ` NN0 ) } ) e. _V $=
      ( cn0 cund cfv csn nn0ex snex unex ) AABCZDEHFG $.

    $( [5-Sep-2014] $)
    fun-is-parf $p |- ( ( A e. NN0 /\ B : ( NN0 ^m ( 1 ... A ) ) --> ( NN0 u. {
        ( Undef ` NN0 ) } ) ) -> B e. ( RecParFa ` A ) ) $=
      ( cn0 wcel c1 cfz co cmap cund cfv csn wf wa crecparfa compactified-nn-ex
      cun ovex elmap biimpri adantl wceq dfrecparfa1 adantr eleqtrrd ) ACDZCEAF
      GZHGZCCIJKPZBLZMBUHUGHGZANJZUIBUJDZUEULUIUHUGBOCUFHQRSTUEUKUJUAUIAUBUCUD
      $.

    $( [5-Sep-2014] $)
    zer-fn $p |- RecZer : ( NN0 ^m ( 1 ... 0 ) ) --> NN0 $=
      ( va cc0 cn0 wcel c1 cfz co cmap creczer wf wral df-reczer fmpt biimpi cv
      0nn0 a1i mprg ) BCDZCEBFGHGZCIJZATSATKUAATCBIALMNSAOTDPQR $.

    $( [5-Sep-2014] $)
    zer-totfa $p |- RecZer e. ( RecTotFa ` 0 ) $=
      ( cc0 cn0 wcel c1 cfz co cmap creczer wf crectotfa cfv zer-fn fun-is-totf
      0nn0 mp2an ) ABCBDAEFGFBHIHAJKCNLAHMO $.
      $( [5-Sep-2014] $)

    $( needs more lemmas about elements of integer ranges. $)
    suc-fn $p |- RecSuc : ( NN0 ^m ( 1 ... 1 ) ) --> NN0 $=
      ( va c1 cv cfv caddc cn0 wcel cfz cmap crecsuc wral df-recsuc fmpt biimpi
      co wf nn0ex ovex elmap wceq eqid1 1nn0 elexi elsnc mpbir cz 1z fzsn ax-mp
      csn eleqtrri ffvelrn mpan2 peano2nn0 3syl mprg ) BACZDZBEOZFGZFBBHOZIOZFJ
      PZAVBUTAVBKVCAVBFUSJALMNUQVBGZVAFUQPZURFGZUTVDVEFVAUQQBBHRSNVEBVAGVFBBUJZ
      VABVGGBBTBUABBBFUBUCUDUEBUFGVAVGTUGBUHUIUKVAFBUQULUMURUNUOUP $.

    $( [5-Sep-2014] $)
    suc-totfa $p |- RecSuc e. ( RecTotFa ` 1 ) $=
      ( c1 cn0 wcel cfz co cmap crecsuc wf crectotfa cfv 1nn0 fun-is-totf mp2an
      suc-fn ) ABCBAADEFEBGHGAIJCKNAGLM $.
      $( [5-Sep-2014] $)

  $} $(

    prj-value @p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) = ( a e. ( NN0 ^m ( 1 ... B ) ) |-> if ( A <_ B , ( a ` A ) , 0 ) ) ) @= ? @.
    prj-val2  @p |- ( ( A e. NN /\ B e. NN /\ A <_ B ) -> ( A RecPrj B ) = ( z e. ( NN0 ^m ( 1 ... B ) ) |-> ( z ` A ) ) ) @= ? @.
    prj-val3  @p |- ( ( ( A e. NN /\ B e. NN /\ A <_ B ) /\ C e. ( NN0 ^m ( 1 ... B ) ) ) -> ( ( A RecPrj B ) ` C ) = ( C ` A ) ) @= ? @.
    prj-fun   @p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) Fun ( NN0 ^m ( 1 ... B ) ) ) @= ? @.
    prj-fn    @p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) : ( NN0 ^m ( 1 ... B ) ) --> NN0 ) @= ? @.
    prj-totfa @p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) e. ( RecTotFa ` B ) ) @= ? @.
    sub-totfa @p |- ( ( ( A e. NN /\ B e. NN ) /\ ( C e. ( RecTotFa ` A ) /\ D e. ( ( RecTotFa ` B ) ^m ( 1 ... A ) ) ) ) -> ( C ( A RecSub B ) D ) e. ( RecTotFa ` B ) ) @= ? @.
    sub-parfa @p |- ( ( ( A e. NN /\ B e. NN ) /\ ( C e. ( RecParFa ` A ) /\ D e. ( ( RecParFa ` B ) ^m ( 1 ... A ) ) ) ) -> ( C ( A RecSub B ) D ) e. ( RecParFa ` B ) ) @= ? @.
    prc-totfa @p |- ( ( A e. NN /\ B e. ( RecTotFa ` A ) /\ C e. ( RecTotFa ` ( A + 1 ) ) ) -> ( B ( RecPrc ` A ) C ) e. ( RecTotFa ` ( A + 1 ) ) ) @= ? @.
    prc-parfa @p |- ( ( A e. NN /\ B e. ( RecParFa ` A ) /\ C e. ( RecParFa ` ( A + 1 ) ) ) -> ( B ( RecPrc ` A ) C ) e. ( RecParFa ` ( A + 1 ) ) ) @= ? @.
    sea-parfa @p |- ( ( A e. NN /\ B e. ( RecParFa ` ( A + 1 ) ) ) -> ( ( RecSea ` A ) ` B ) e. ( RecParFa ` A ) ) @= ? @.
@}

@{
    @d a b c d e f g @.

    @( we probably need to go finer grained than this @)

    prim-is-gen-lem0 @p |- ( ( B C_ ( NN0 X. RecParF ) /\ A C_ B ) -> ( RecArithPrimitiveStep ` A ) C_ ( RecArithPrimitiveStep ` B ) ) @= ? @.
    prim-is-gen-lem1 @p |- ( ( B C_ ( NN0 X. RecParF ) /\ A C_ B ) -> ( RecArithGeneralStep ` A ) C_ ( RecArithGeneralStep ` B ) ) @= ? @.
    prim-is-gen-lem2 @p |- ( A C_ ( NN0 X. RecParF ) -> ( RecArithPrimitiveStep ` A ) C_ ( RecArithGeneralStep ` A ) ) @= ? @.
    prim-is-gen-lem3 @p |- ( X e. On -> ( RecArithPrimitiveL ` X ) C_ ( RecArithGeneralL ` X ) ) @= ? @.
    prim-is-gen-arith @p |- RecArithPrimitive C_ RecArithGeneral @= ? @.
    prim-is-gen @p |- RecPrimitive C_ RecGeneral @= ? @.

    @( not super sure how to prove these @)

    gen-arith-isfun @p |- Fun RecArithGeneral @= ? @.
    gen-arith-dom @p |- dom RecArithGeneral C_ NN @= ? @.
    gen-are-parf @p |- RecGeneral C_ RecParF @= ? @.

    @( easy consequences of the above, except for prim-are-totf @)
    prim-arith-isfun @p |- Fun RecArithPrimitive @= ? @.
    prim-arith-dom @p |- dom RecArithPrimitive C_ NN @= ? @.
    prim-are-totf @p |- RecPrimitive C_ RecTotF @= ? @.

    @( nonconstructive cardinality proof.  we will see the explicit diagonalization construction later @)
    ex-nongen-totf-card-lem0 @p |- RecGeneral ~< NN @= ? @.
    ex-nongen-totf-card-lem1 @p |- RecParF ~~ ~P NN @= ? @.
    ex-nongen-totf-card @p |- RecGeneral C. RecParF @= ? @.
@}

@{
    @( construction and induction principles @)

    zer-arith-prim @p |- <. ( 1 ,n 0 ) , RecZer >. e. RecPrimitive @= ? @.
    suc-arith-prim @p |- <. ( 1 ,n 1 ) , RecSuc >. e. RecPrimitive @= ? @.
    prj-arith-prim @p |- ( ( A e. NN /\ B e. NN /\ A <_ B ) -> <. ( 2 ,n ( A ,n B ) ) , ( A RecPrj B ) >. e. RecPrimitive ) @= ? @.

    zer-prim @p |- RecZer e. RecPrimitive @= ? @.
    suc-prim @p |- RecSuc e. RecPrimitive @= ? @.

    prim-en-nn @p |- RecPrimitive ~~ NN @= ? @.
    gen-en-nn @p |- RecGeneral ~~ NN @= ? @.

    @( We may not need a full induction schema; coinduction + cantor pair comparison lemmata implies that ordinary induction on NN0 can be lifted to induction here @)
    @( generally have +, -, *, /, 1st_n, 2nd_n, ,n, all constants, bounded looping, bounded iota, composition (normal subsititute-y), anything else we might need @)
@}

@{
    @( tree recursion lemma: reifies the stacks, takes p.r. f, g, fc, gc, h and builds F:
       F(x) = h( x, fc(x) ? F(f(x)) : 0, gc(x) ? F(g(x)) : 0 )  details TBD @)
    @( F is general recursive @)
    @( F is total if there exists T : NN --> On which is decreased by f and g @)
    @( F is primitive recursive if there exists T : NN -> NN which is primitve recursive and T(f(x)) + T(g(x)) < T(x) @)
@}

@{
    @( succinct encodings @)
    @( ( x -> 2*x ) has some number < A = A ^ ( k ^ 0 ) @)
    @( ( x -> 2*x + 1 ) has some number < A ^ ( k ^ 0 ) @)
    @( if A >= A_base and f# < A and g# < A, (f o. g)# < A ^ k @)
    @( for i = 0, all N < 2 ^ ( 2 ^ i ), ( x -> (2^(2^i))*x + N )# < A ^ ( k ^ 0 ) @)
    @( for i >= 0, N < 2 ^ ( 2 ^ ( i + 1 ) ), ( x -> (2^(2^(i+1)))*x + N ) = ( x -> (2^(2^i))*x + A ) o. ( x -> (2^(2^i))*x + B ) for A,B determined by the division theorem @)
    @( for i >= 0, N < 2 ^ ( 2 ^ i ), ( x -> (2^(2^i))*x + N )# < A ^ ( k ^ i ) by induction @)
    @( for x >= 0, exists i such that x <_ ( 2 ^ ( 2 ^ i ) ) <_ ( x ^ 2 ) @)
    @( for x >= 0, ( () -> x )# < ( A ^ ( k ^ i ) ) -> log( () -> x ) <
       log( A ^ ( k ^ i ) ) = (k^i).log(A) = (2^i)^(log(k)/log(2))*log(A) <
       log(A)/log(2)*log(2^2^i)^(log(k)/log(2)) <
       log(A)/log(2) * log(x^2) ^ (log(k)/log(2)) = K * log(x) ^ L @)

@}

@{
    @( Raphael Robinson's inductive intrinsic characterization of the one-argument p.r. functions.  use ( ( ( x ,n b ) - a ) ,n a ) as an increment-friendly pair that works with our lemmas @)
@}

@{
    @( Peter-Ackermann function @)
    @( A(0)   = Suc @)
    @( A(i+1) = Prc(A(i),A(i)) @)
    @( A(i,_) is primitive recursive at level i @)
    @( let P(i) = for all p.r. F at level i and all [x...], F(x...) <_ A(max(x...)) @)
    @( P(0) : F at 0 is Zer, Suc, or Prj @)
    @( P(i+1) : zer/suc/prj handled.  either Sub or Prc remains @)
    @( Prj(f,g)(const,N) : note g(const) <_ A(const), for all v >= max(const) (f(const,i) <_ partial ackerman) @)
    @( requires A_i(i) is monotonic @)
    @( requires definition of iterates of A @)
    @( Sub(f,g...) : note all g values are less than A_i(in), so the result is less than A_i(A_i(in)) @)
    @( requires: A(i,A(i,x)) <_ A(i+1,x) @)
    @( requires: A(i,j) is strictly monotonic in i,j @)
    @( A(j,j) is not dominated by A(i,j) for any fixed i @)
    @( A(j,j) is not primitive recursive @)
    @( suppose phi(f#, x) were primitive recursive.  then f(x) <_ A(i,max(f#,x)) for some i and all pr f @)
    @( let f = A(i+1,_), y = f#.  A(i+1,y) = f(y) <_ A(i,max(f#,y)) = A(i,y), contradicting A(i+1,y) > A(i,j) @)
    @( thus phi is not pr.  it will be shown gr in the next section @)
    @( todo: this does not seem to quite be the standard Peter-Ackerman function, which has A(i+1) = Prc(A(i),1).  I like how much sharper my version is, the fastest-growing PR function of a given rank.  OTOH it's a little harder to calculate @)
@}

@{
    @( Relativization and the Turing Degrees? @)
@}

@( ---- HALTING ---- @)
@( Prove the existance of a Universal Turing Machine (i.o.w. the Turing evaluation function is a partial computable function) and formalize the existance of semidecidable predicates that are not decidable. @)

@( doing this by recursion theory now.
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
@)

eval-recursive @p |- ( x e. ( NN0 ^m ( 1 ... 2 ) ) |-> if ( ( x ` 1 ) e. dom RecArithGeneral , ( ( RecArithGeneral ` ( x ` 1 ) ) ` ( { 1 } X. { ( x ` 2 ) } ) ) , ( Undef ` NN0 ) ) ) e. RecArithGeneral @= ? @.

$)

$( ---- MULTIVARIATE POLYNOMIALS ---- $)
$( Define multivariate polynomials and prove that they include constants and projections and are closed under addition, multiplication, and renaming of variables. Later we will also need the property that polynomial functions are computable. $)
$( in particular, we don't need normal forms, so just define these as a recursive set $)


$( ---- MATIYASEVICH 1 ---- $)
$( Diophantine sets are semidecidable because polynomial functions are computable. $)

$( ---- MATIYASEVICH 2 ---- $)
$( Semidecidable sets are decidable by Turing machines, which can be expressed as vectorial and thus exponential satisfaction problems and are Diophantine. $)

$( ---- MATIYASEVICH 3 ---- $)
$( Diophantine <-> Semidecidable.  There exist non-decidable diophantine sets. $)

  $( Unrelated:  Wiener pairs treat proper classes symmetrically. $)
  wopprc $p |- ( ( A e. _V /\ B e. _V ) <-> -. 1o e. { { { A } , (/) } , { { B
      } } } ) $=
    ( cvv wcel wa c0 csn cpr wn c1o wceq wo pm4.56 snex 0ex snprc impbii notbii
    con2bii bitr4i dfsn2 id syl5reqr preqr1 sylibr biimpi preq1d syl6reqr eqcom
    syl bitr2i sneqr sneq anbi12i elpr 3bitr4i df1o2 eleq1i ) ACDZBCDZEZFGZAGZF
    HZBGZGZHZDZIZJVGDZIVBVDKZIZVBVFKZIZEVKVMLZIVAVIVKVMMUSVLUTVNVKUSVKUSIZVKVCF
    KZVPVKVDFFHZKVQVKVRVBVDFUAZVKUBUCVCFFANOUDUJAPZUEVPVDVRVBVPVCFFVPVQVTUFUGVS
    UHQSUTFVEKZIVNWAUTUTIVEFKWABPVEFUIUKSVMWAVMWAFVEOULFVEUMQRTUNVHVOVBVDVFFNUO
    RUPVJVHJVBVGUQURRT $.
    $( [19-Sep-2014] $)

  $( Membership in a set of upper integers in terms of subtraction. $)
  uzsubnn0 $p |- ( A e. ( ZZ>= ` B ) -> ( A - B ) e. NN0 ) $=
    ( cuz cfv wcel cmin co cc0 cn0 cz caddc 0z a1i eluzel2 wceq zcn addid2 3syl
    id cc fveq2d eleqtrrd eluzsub syl3anc nn0uz syl6eleqr ) ABCDZEZABFGZHCDZIUH
    HJEZBJEZAHBKGZCDZEUIUJEUKUHLMBANZUHAUGUNUHSUHUMBCUHULBTEUMBOUOBPBQRUAUBBHAU
    CUDUEUF $.
    $( [5-Oct-2014] $)

  ${
    $d x y A $.  $d x y B $.  $d x y $.
    n0reeor.1 $e |- ( ph -> A. y ph ) $.
    n0reeor.2 $e |- ( ps -> A. x ps ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    n0reeor $p |- ( ( A =/= (/) /\ B =/= (/) ) -> ( E. x e. A E. y e. B ( ph \/
        ps ) <-> ( E. x e. A ph \/ E. y e. B ps ) ) ) $=
      ( wo wrex c0 wne r19.43 wb cv wcel idd rexlimi wral wal rexbii syl r19.2z
      wa bitri alral syl5 impbid2 rexbidv adantl rexcom syl5bb adantr orbi12d
      ex ) ABIDFJZCEJZADFJZCEJZBDFJZCEJZIZEKLZFKLZUDZACEJZUTIUQURUTIZCEJVBUPVGC
      EABDFMUAURUTCEMUEVEUSVFVAUTVDUSVFNVCVDURACEVDURAAADFGDOFPAQRAADFSZVDURAAD
      TVHGADFUFUBVDVHURADFUCUOUGUHUIUJVCVAUTNVDVABCEJZDFJVCUTBCDEFUKVCVIBDFVCVI
      BBBCEHCOEPBQRBBCESZVCVIBBCTVJHBCEUFUBVCVJVIBCEUCUOUGUHUIULUMUNUL $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d ph y $.  $d ps x $.  $d x y A $.  $d x y B $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    n0reeorv $p |- ( ( A =/= (/) /\ B =/= (/) ) -> ( E. x e. A E. y e. B ( ph
        \/ ps ) <-> ( E. x e. A ph \/ E. y e. B ps ) ) ) $=
      ( ax-17 n0reeor ) ABCDEFADGBCGH $.
      $( [5-Oct-2014] $)
  $}


  $( early warmup proofs.  I may find a use for Id ` x. later. $)
  wu0 $p |- ( ( ZZ ^m ( 1 ... 0 ) ) X. { 0 } ) e. ( ZZ ^m ( ZZ ^m ( 1 ... 0 ) )
      ) $=
    ( cc0 csn cz c1 cfz co cmap cxp wss wcel 0z snssi ax-mp ovex mapss wf elexi
    zex fconst snex elmap mpbir sselii ) ABZCDAEFZGFZGFZCUFGFZUFUDHZUDCIZUGUHIA
    CJUJKACLMUDCUFRCUEGNZOMUIUGJUFUDUIPUFAACKQSUDUFUIATUKUAUBUC $.
    $( [19-Oct-2014] $)
  ${
    $d u x $.  $d a b $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    wu8 $p |- ( u e. CC -> ( A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) ->
        u = 1 ) ) $=
      ( cv cc wcel cmul co wceq wa wral c1 wi ax-1cn ax-17 oveq2 id eqeq12d a1i
      simpl syld oveq1 anbi12d rcla4 ax-mp mulid1 syl simpr eqtr3d ex ) BCZDEZU
      JACZFGZULHZULUJFGZULHZIZADJZUJKFGZKHZKUJFGZKHZIZUJKHZURVCLZUKKDEVEMUQVCAK
      DVCANULKHZUNUTUPVBVFUMUSULKULKUJFOVFPZQVFUOVAULKULKUJFUAVGQUBUCUDRUKVCUTV
      DVCUTLUKUTVBSRUKUTVDUKUTIZUSUJKVHUKUSUJHUKUTSUJUEUFUKUTUGUHUITT $.

    $( [30-Aug-2014] $)
    wu7 $p |- ( u e. CC -> ( u = 1 -> A. x e. CC ( ( u x. x ) = x /\ ( x x. u )
        = x ) ) ) $=
      ( cv c1 wceq cmul co wa cc wral wcel mulid2 mulid1 jca a1i ralrimiv ax-17
      wi eqcom eqeq1d biimpi oveq1d oveq2d anbi12d ralbid mpbid ) BCZDEZUGACZFG
      ZUIEZUIUGFGZUIEZHZAIJZRUGIKUHDUIFGZUIEZUIDFGZUIEZHZAIJUOUHUTAIUIIKZUTRUHV
      AUQUSUILUIMNOPUHUTUNAIUHAQUHUQUKUSUMUHUPUJUIUHDUGUIFUHDUGEUGDSUAZUBTUHURU
      LUIUHDUGUIFVBUCTUDUEUFO $.

    $( [30-Aug-2014] $)
    wu6 $p |- ( ( T. /\ 1 e. C /\ u e. CC ) -> ( A. x e. CC ( ( u x. x ) = x /\
        ( x x. u ) = x ) <-> u = 1 ) ) $=
      ( wtru c1 wcel cv cc w3a cmul co wceq wa wral wb simp3 wu8 wu7 impbid syl
      ) DECFZBGZHFZIUCUBAGZJKUDLUDUBJKUDLMAHNZUBELZODUAUCPUCUEUFABQABRST $.

    $( [30-Aug-2014] $)
    wu5 $p |- ( iota_ u e. CC A. x e. CC ( ( u x. x ) = x /\ ( x x. u ) = x ) )
        = 1 $=
      ( wtru c1 cc wcel wa cv cmul co wceq wral crio ax-1cn pm3.2i riota5 ax-mp
      tru wu6 ) CDEFZGBHZAHZIJUBKUBUAIJUBKGAELZBEMDKCTRNOCUCBEDABESPQ $.

    $( [30-Aug-2014] $)
    wu10 $p |- x. : ( CC X. CC ) -onto-> CC $=
      ( vb va cc cxp cmul wfo wf cv cfv wceq wrex wral dffo3 ax-mulopr wcel a1i
      c1 wa jca syl ax-1cn id opelxpi co mulid2 eqcomd df-ov eqtrd fveq2 eqeq2d
      cop rcla4ev rgen mpbir2an ) CCDZCEFUOCEGAHZBHZEIZJZBUOKZACLBAUOCEMNUTACUP
      COZQUPUKZUOOZUPVBEIZJZRUTVAVCVEVAQCOZVARVCVAVFVAVFVAUAPVAUBSQUPCCUCTVAUPQ
      UPEUDZVDVAVGUPUPUEUFVGVDJVAQUPEUGPUHSUSVEBVBUOUQVBJURVDUPUQVBEUIUJULTUMUN
      $.

    $( [30-Aug-2014] $)
    wu9 $p |- ( Id ` x. ) = 1 $=
      ( va vb cmul cgi cfv cv co wceq wa cc wral crio c1 cvv wcel mulex crn cxp
      wfo ax-mp wu10 forn eqcomi gidval wu5 eqtri ) CDEZAFZBFZCGUIHUIUHCGUIHIBJ
      KAJLZMCNOUGUJHPBACNJCQZJJJRZJCSUKJHUAULJCUBTUCUDTBAUEUF $.
      $( [30-Aug-2014] $)
  $}



$( TODO / IWBNI
    Things I've wanted.  If I still want them after I'm more familiar with the system, I'll implement/call for them
    1. Cheat sheet of "do you want to do this -> use these theorems".  tell people to take advantage of min *
    2. WRITE SOURCE with $[ $] would make my life much easier
    3. Namespaces - see separate doc
    4. How to handle similar subtrees in the PA: command to copy a subtree to a new node, either with or without syntax proofs(?).  An easy way to create new lemmas from completely proved subtrees without losing PA state would be nice.
        or, create a lemma from a part of a completely proved theorem.  that would be nice.
    5. proof mangling?
    6. ;-commands.  control over prompting
    7. disjoint variables in PA would save me much time
    8. vim highlighting
    9. PA should collapse identical proof stages; possibly add an improve option to seek out commonality by using incomplete subtrees
    10. experiment with the proof shrinking potential of deduction versions of the algebra theorems
        10b. <. A , B >. = if ( B e. _V , { A , { A , B } } , 1o )
    11. PA should display [-NN] in sh n/u listing
    12. automatic improve and loud warning when a ground wff cannot be proved?
    13. command to list changed proofs
    14. I just reproved 19.26 because I had no way of finding it :x
    15. Last command in HELP DEMO is wrong ( (_ is C_ )
    16. Some kind of macro/repeat command.  Needs much more though
    17. Pony: PA working directly on compressed proofs
    18. Pony: Pluggable decision procedures
    19. MATCH would be much more awesome if it took a name wildcard
    20. Blank lines before/after SHOW PROOF would help
    21. backrefs in SEARCH
    22. how can the PA (in particular SHOW PROOF) be made more usable with very large proofs?  common syntax-subtree mining / abbrevification?  reduce indent without going all the way to LEMMON?  better control over the proof tree fragment to display?
    23. Pony: catch SIGINT, make MINIMIZE_WITH and IMPROVE interruptable, suppress output
    24. IMPROVE LHF: switch to iterated deepening to avoid idiVD, use the first of a set of equivalent theorems to avoid grothomex syndrome ( but prefer axioms if later )
    25. SHOW STATEMENT NEW would be cool
    26. ASSIGN with $e does not work as described.  it would be much more useful if out of scope $e's were excluded
    27. /WIDTH to SHOW PROOF
    28. LET [VAR] $1 = $2 = ...
    29. LET STEP seems possibly nonfunctional, need to investigate
    30. V P {MY-MATHBOX}
    31. MMPE: hover over GIFs to see original math symbol?
    32. MMPE: hover over subexpression, see "parse" (highlight smallest wff/class around cursor)?
$)

$( (End of Stefan O'Rear's mathbox.) $)
