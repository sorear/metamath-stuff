$[ set_clean.mm $] $( set.mm - Version of 12-Nov-2014 $)

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
  $( negmod0 $)
  $( absmod0 $)


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
       sets._ (Contributed by Stefan O'Rear, 30-Aug-2014.) $)
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
    $( Post-composition (renaming indexes) of a mapping viewed as a point.
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mapco2 $p |- ( ( A e. ( B ^m C ) /\ D : E --> C ) -> ( A o. D ) e. ( B ^m E
        ) ) $=
      ( cmap co wcel wf wa ccom elmap fco sylanb sylibr ) ABCIJKZECDLZMEBADNZLZ
      UABEIJKSCBALTUBBCAFGOECBADPQBEUAFHOR $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d a b c d $.
    $( Eliminate antecedent for mapping theorems: domain can be taken to be a
       set.  (Contributed by Stefan O'Rear, 8-Oct-2014.) $)
    elmapex1 $p |- ( A e. ( B ^m C ) -> B e. _V ) $=
      ( va vb vd vc cmap co wcel c0 wceq cvv n0i cdm wrel cv wa wf cab df-mpt2
      copab2 reldmoprab cmpt2 df-map eqtri dmeqi releqi mpbir ovprc1 nsyl2 ) AB
      CHIZJULKLBMJULANBCHHOZPDQZMJEQZMJRFQUOUNGQSGTZLRZDEFUBZOZPUQDEFUCUMUSHURH
      DEMMUPUDURDEGUEDEFMMUPUAUFUGUHUIUJUK $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A c $.  $d B c $.  $d C c $.
    $( A mapping always has some domain, even if the notional domain is a
       proper class.  Uses ~ ovprc2 inessentially.  (Contributed by Stefan
       O'Rear, 8-Oct-2014.) $)
    elmapex2 $p |- ( A e. ( B ^m C ) -> E. c A e. ( B ^m c ) ) $=
      ( cvv wcel cmap co cv wex wi wceq oveq2 eleq2d cla4egv wn ovprc2 elmapex1
      mpcom syl6bi pm2.61i ) CEFZABCGHZFZABDIZGHZFZDJZKUGUDDCEUECLUFUCAUECBGMNO
      UBPZUDABBGHZFZUHUIUCUJABCGQNBEFUKUHABBRUGUKDBEUEBLUFUJAUEBBGMNOSTUA $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A c $.  $d B c $.  $d C c $.
    $( A mapping is always a function (even if C is a proper class)
       (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
    elmapfun $p |- ( A e. ( B ^m C ) -> Fun A ) $=
      ( vc cmap co wcel cv wex wfun elmapex2 wf cvv elmapex1 vex elmapg sylancl
      wb ibi syl ffun exlimiv ) ABCEFGABDHZEFGZDIAJZABCDKUDUEDUDUCBALZUEUDUFUDB
      MGUCMGUDUFRABUCNDOBUCAMMPQSUCBAUATUBT $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b c $.  $d B a b c $.  $d C a b c $.  $d D a b c $.  $d E a b c $.
    $( Renaming indexes in a tuple, with sethood as antecedents.  (Contributed
       by Stefan O'Rear, 9-Oct-2014.) $)
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

  $( A restricted mapping is a mapping.  (Contributed by Stefan O'Rear,
     9-Oct-2014.) $)
  elmapssres $p |- ( ( A e. ( B ^m C ) /\ D C_ C /\ C e. _V ) -> ( A |` D ) e.
      ( B ^m D ) ) $=
    ( cmap co wcel wss cvv w3a cres wf simp1 wb elmapex1 3ad2ant1 simp3 syl2anc
    elmapg mpbid simp2 fssres ssexg 3adant1 mpbird ) ABCEFGZDCHZCIGZJZADKZBDEFG
    ZDBUJLZUICBALZUGULUIUFUMUFUGUHMUIBIGZUHUFUMNUFUGUNUHABCOPZUFUGUHQBCAIISRTUF
    UGUHUACBDAUBRUIUNDIGZUKULNUOUGUHUPUFDCIUCUDBDUJIISRUE $.
    $( [9-Oct-2014] $)

  $( A mapping is a function, forward direction only with superfluous
     antecedent removed.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
  elmapi $p |- ( ( C e. _V /\ A e. ( B ^m C ) ) -> A : C --> B ) $=
    ( cvv wcel cmap co wa wf simpr elmapex1 adantl simpl elmapg syl2anc mpbid
    wb ) CDEZABCFGEZHZSCBAIZRSJTBDEZRSUAQSUBRABCKLRSMBCADDNOP $.
    $( [10-Oct-2014] $)

  ${
    $d N a b c x $.  $d A a b c x $.  $d B a b c x $.  $d C a b c x $.
    $d D a b c x $.  $d M a b c x $.
    mapfzcons.1 $e |- M = ( N + 1 ) $.
    $( Extending a one-based mapping by adding a tuple at the end results in
       another mapping.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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

    $( Recover prefix mapping from an extended mapping.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
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

    $( A nonempty mapping has a prefix.  (Contributed by Stefan O'Rear,
       10-Oct-2014.) $)
    mapfzcons1cl $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... M ) ) ) -> ( A |` (
        1 ... N ) ) e. ( B ^m ( 1 ... N ) ) ) $=
      ( cn0 wcel c1 cfz co cmap wa wss cres simpr caddc fzssp1 oveq2i syl6sseqr
      cvv adantr ovex a1i elmapssres syl3anc ) DFGZABHCIJZKJGZLZUHHDIJZUGMZUGTG
      ZAUJNBUJKJGUFUHOUFUKUHUFUJHDHPJZIJUGHDFQCUMHIERSUAULUIHCIUBUCABUGUJUDUE
      $.
      $( [10-Oct-2014] $)

    $( Recover added element from an extended mapping.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
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
       notation.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
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
       definition.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    mptfcl $p |- ( ( t e. A |-> B ) : A --> C -> ( t e. A -> B e. C ) ) $=
      ( cmpt wf wcel wral cv wi eqid fmpt ra4 sylbir ) BDABCEZFCDGZABHAIBGPJABD
      COOKLPABMN $.
      $( [10-Oct-2014] $)
  $}


  ${
    $d F a b c $.  $d A a b c $.  $d G a b c $.  $d V a b c $.  $d X a b c $.
    $d R a b c $.

    $( Function value of a pointwise composition.  (Contributed by Stefan
       O'Rear, 5-Oct-2014.) $)
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
       sequence.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    fcompt $p |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |->
        ( A ` ( B ` x ) ) ) ) $=
      ( wf wa ccom cv cfv cmpt wfn wceq crn wss ffn adantr adantl frn fnco wfun
      syl3anc dffn5v sylib ffun wcel fvco2 3expa mpteq2dva syl2an eqtrd ) EFBGZ
      DECGZHZBCIZADAJZUPKZLZADUQCKBKZLZUOUPDMZUPUSNUOBEMZCDMZCOEPZVBUMVCUNEFBQR
      UNVDUMDECQZSUNVEUMDECTSEDBCUAUCADUPUDUEUMBUBZVDUSVANUNEFBUFVFVGVDHADURUTV
      GVDUQDUGURUTNDUQBCUHUIUJUKUL $.
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
    $d f g i j p v x $.
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
    $d V v p f g a b c $.  $d V v p i a b c $.  $d V v p j x a b c $.
    $( Substitution lemma for ` mzPolyCld ` .  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpclval $p |- ( V e. _V -> ( mzPolyCld ` V ) = { p | ( p C_ ( ZZ ^m ( ZZ
        ^m V ) ) /\
        ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. p
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. p )
        /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) )
        } ) $=
      ( va vc vb cvv wcel cfv cv cz cmap co wral cmpt wa cmzpcl wss csn cxp cof
      caddc cmul cab wceq oveq2d sseq2d xpeq1d eleq1d ralbidv mpteq1 raleqbi1dv
      vv oveq2 syl anbi12d anbi1d abbidv df-mzpcl ovex abssexg ax-mp fvmpt sneq
      xpeq2d cbvralv fveq2 mpteq2dv cbvmptv eleq1i syl6bb anbi12i anbi1i anbi2i
      weq fveq1 abbii syl6eq ) FKLFUAMGNZOOFPQZPQZUBZWDHNZUCZUDZWCLZHORZIWDJNZI
      NZMZSZWCLZJFRZTZBNZCNZUFUEQWCLWSWTUGUEQWCLTCWCRBWCRZTZTZGUHZWFWDDNZUCZUDZ
      WCLZDORZAWDENZANZMZSZWCLZEFRZTZXATZTZGUHUQFWCOOUQNZPQZPQZUBZXTWHUDZWCLZHO
      RZIXTWNSZWCLZJXSRZTZXATZTZGUHXDKUAXSFUIZYKXCGYLYBWFYJXBYLYAWEWCYLXTWDOPXS
      FOPURZUJUKYLYIWRXAYLYEWKYHWQYLYDWJHOYLYCWIWCYLXTWDWHYMULUMUNYGWPJXSFYLYFW
      OWCYLXTWDUIYFWOUIYMIXTWDWNUOUSUMUPUTVAUTVBIUQBCHJGVCWEKLXDKLOWDPVDXBGWEKV
      EVFVGXCXRGXBXQWFWRXPXAWKXIWQXOWJXHHDOHDVSZWIXGWCYNWHXFWDWGXEVHVIUMVJWPXNJ
      EFJEVSZWPIWDXJWMMZSZWCLXNYOWOYQWCYOIWDWNYPWLXJWMVKVLUMYQXMWCIAWDYPXLXJWMX
      KVTVMVNVOVJVPVQVRWAWB $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d V v p f g $.  $d V v p i $.  $d V v p j x $.  $d P v p f g $.
    $d P v p i $.  $d P v p j x $.
    $( Double substitution lemma for ` mzPolyCld ` .  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
    elmzpcl $p |- ( ( V e. _V /\ P e. _V ) -> ( P e. ( mzPolyCld ` V ) <-> ( P
        C_ ( ZZ ^m ( ZZ ^m V ) ) /\
        ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. P
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. P )
        /\ A. f e. P A. g e. P ( ( f oF + g ) e. P /\ ( f oF x. g ) e. P ) ) )
        ) ) $=
      ( vp cvv wcel cfv cv cz cmap co wss wral wa eleq2 anbi12d cmzpcl csn cmpt
      cxp caddc cof cmul mzpclval eleq2d wceq sseq1 ralbidv raleqbi1dv sylan9bb
      cab elabg ) GIJZBGUAKZJBHLZMMGNOZNOZPZUTELUBUDZUSJZEMQZAUTFLALKUCZUSJZFGQ
      ZRZCLZDLZUEUFOZUSJZVJVKUGUFOZUSJZRZDUSQZCUSQZRZRZHUOZJBIJBVAPZVCBJZEMQZVF
      BJZFGQZRZVLBJZVNBJZRZDBQZCBQZRZRZUQURWABACDEFGHUHUIVTWNHBIUSBUJZVBWBVSWMU
      SBVAUKWOVIWGVRWLWOVEWDVHWFWOVDWCEMUSBVCSULWOVGWEFGUSBVFSULTVQWKCUSBVPWJDU
      SBWOVMWHVOWIUSBVLSUSBVNSTUMUMTTUPUN $.
      $( [4-Oct-2014] $)
  $}

  ${
    $d V v p f g a b $.  $d P v p f g a b $.  $d F v p f g a b $.
    $d G v p f g a b $.
    $( The set of all functions with the signature of a polynomial is a
       polynomially closed set.  This is a lemma to show that the intersection
       in ~ df-mzp is well defined.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpclall $p |- ( V e. _V -> ( ZZ ^m ( ZZ ^m V ) ) e. ( mzPolyCld ` V ) ) $=
      ( vv vf vg va vb cz cv cmap co cmzpcl cfv wcel cvv wral wa caddc wf elmap
      zex wceq oveq2 oveq2d fveq2 eleq12d wss csn cxp cmpt cof cmul wb vex ovex
      elmzpcl mp2an ssid constmap rgen ffvelrn sylanb ancoms eqid sylibr pm3.2i
      wel fmptd zaddcl adantl simpl simpr a1i off zmulcl anbi12i 3imtr4i rgen2a
      inidm jca mpbir2an vtoclg ) GGBHZIJZIJZWBKLZMZGGAIJZIJZAKLZMBANWBAUAZWDWH
      WEWIWJWCWGGIWBAGIUBUCWBAKUDUEWFWDWDUFZWCCHZUGUHWDMZCGOZDWCWLDHZLZUIZWDMZC
      WBOZPZWLWOQUJJZWDMZWLWOUKUJJZWDMZPZDWDOCWDOZPZWBNMWDNMWFWKXGPULBUMZGWCIUN
      DWDCDCCWBUOUPWDUQWTXFWNWSWMCGWCWLGGWBIUNZCUMTURUSWRCWBCBVFZWCGWQRWRXJDWCW
      PGWQWOWCMZXJWPGMZXKWBGWORXJXLGWBWOTXHSWBGWLWOUTVAVBWQVCVGGWCWQTXISVDUSVEX
      ECDWDWCGWLRZWCGWORZPZWCGXARZWCGXCRZPWLWDMZWOWDMZPXEXOXPXQXOEFWCWCWCQGGGWL
      WONNEHZGMFHZGMPZXTYAQJGMXOXTYAVHVIXMXNVJZXMXNVKZWCNMXOXIVLZYEWCVRZVMXOEFW
      CWCWCUKGGGWLWONNYBXTYAUKJGMXOXTYAVNVIYCYDYEYEYFVMVSXRXMXSXNGWCWLTXISGWCWO
      TXISVOXBXPXDXQGWCXATXISGWCXCTXISVOVPVQVEVTWA $.
      $( [4-Oct-2014] $)

    $( Corrolary of ~ mzpclall :  Polynomially closed function sets are not
       empty.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    mzpcln0 $p |- ( V e. _V -> ( mzPolyCld ` V ) =/= (/) ) $=
      ( cvv wcel cz cmap co cmzpcl cfv c0 wne mzpclall ne0i syl ) ABCDDAEFEFZAG
      HZCOIJAKONLM $.
      $( [4-Oct-2014] $)

    $( Defining property 1 of a polynomially closed function set ` P ` : it
       contains all constant functions.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
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
       contains all projections.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpcl2 $p |- ( ( V e. _V /\ P e. ( mzPolyCld ` V ) /\ F e. V ) -> ( g e. (
        ZZ ^m V ) |-> ( g ` F ) ) e. P ) $=
      ( vf cvv wcel cmzpcl cfv w3a cz cmap co cv cmpt wral simp3 wa cof syl2anc
      wss csn cxp caddc cmul simp2 wb simp1 elex 3ad2ant2 elmzpcl mpbid simprlr
      syl wceq fveq2 mpteq2dv eleq1d rcla4va ) DFGZADHIZGZCDGZJZVCBKDLMZENZBNZI
      ZOZAGZEDPZBVECVGIZOZAGZUTVBVCQVDAKVELMUAZVEVFUBUCAGEKPZVKRVFVGUDSMAGVFVGU
      ESMAGRBAPEAPZRRZVKVDVBVRUTVBVCUFVDUTAFGZVBVRUGUTVBVCUHVBUTVSVCAVAUIUJBAEB
      EEDUKTULVOVPVKVQUMUNVJVNECDVFCUOZVIVMAVTBVEVHVLVFCVGUPUQURUST $.
      $( [4-Oct-2014] $)

    $( Defining properties 2 of a polynomially closed function set ` P ` : it
       is closed under pointwise addition and multiplication.  (Contributed by
       Stefan O'Rear, 4-Oct-2014.) $)
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
    $( Value of the ` mzPoly ` function.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpval $p |- ( V e. _V -> ( mzPoly ` V ) = |^| ( mzPolyCld ` V ) ) $=
      ( vv cvv wcel cmzpcl cfv cint cmzp wceq c0 wne mzpcln0 intex sylib inteqd
      cv fveq2 df-mzp fvmptg mpdan ) ACDZAEFZGZCDZAHFUCIUAUBJKUDALUBMNBABPZEFZG
      UCCCHUEAIUFUBUEAEQOBRST $.
      $( [4-Oct-2014] $)

    $( ` mzPoly ` is defined for all index sets which are sets.  This is used
       with ~ elfvdm to eliminate sethood antecedents.  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
    dmmzp $p |- dom mzPoly = _V $=
      ( vv cmzp cdm cvv cv cmzpcl cfv cint cmpt df-mzp dmeqi wcel dmmptg c0 wne
      wceq mzpcln0 intex sylib mprg eqtri ) BCADAEZFGZHZIZCZDBUEAJKUDDLZUFDPADA
      DUDDMUBDLUCNOUGUBQUCRSTUA $.
      $( [4-Oct-2014] $)

    $( Polynomial closedness is a universal first-order property and passes to
       intersections.  This is where the closure properties of the polynomial
       ring itself are proved.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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

  $( Constant functions are polynomial.  See also ~ mzpconstmpt .  (Contributed
     by Stefan O'Rear, 4-Oct-2014.) $)
  mzpconst $p |- ( ( V e. _V /\ C e. ZZ ) -> ( ( ZZ ^m V ) X. { C } ) e. (
      mzPoly ` V ) ) $=
    ( cvv wcel cz wa cmzp cfv cmzpcl cmap co csn cxp simpl mzpincl adantr simpr
    mzpcl1 syl3anc ) BCDZAEDZFTBGHZBIHDZUAEBJKALMUBDTUANTUCUABOPTUAQUBABRS $.
    $( [4-Oct-2014] $)

  $( A polynomial function is a function from the coordinate space to the
     integers.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
  mzpf $p |- ( F e. ( mzPoly ` V ) -> F : ( ZZ ^m V ) --> ZZ ) $=
    ( cmzp cfv wcel cz cmap co wf cvv wss cdm elfvdm dmmzp syl6eleq cmzpcl cint
    mzpval mzpclall syl intss1 eqsstrd sselda anidms zex ovex elmap sylib ) ABC
    DZEZAFFBGHZGHZEZUKFAIUJUMUJUIULAUJBJEZUIULKUJBCLJABCMNOUNUIBPDZQZULBRUNULUO
    EUPULKBSULUOUATUBTUCUDFUKAUEFBGUFUGUH $.
    $( [5-Oct-2014] $)

  ${
    $d X g $.  $d V g $.
    $( A projection function is polynomial.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpproj $p |- ( ( V e. _V /\ X e. V ) -> ( g e. ( ZZ ^m V ) |-> ( g ` X ) )
        e. ( mzPoly ` V ) ) $=
      ( cvv wcel wa cmzp cfv cmzpcl cz cmap co cmpt simpl mzpincl adantr mzpcl2
      cv simpr syl3anc ) BDEZCBEZFUABGHZBIHEZUBAJBKLCARHMUCEUAUBNUAUDUBBOPUAUBS
      UCACBQT $.
      $( [4-Oct-2014] $)
  $}

  $( The pointwise sum of two polynomial functions is a polynomial function.
     See also ~ mzpaddmpt .  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
  mzpadd $p |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) -> ( A oF + B )
      e. ( mzPoly ` V ) ) $=
    ( cmzp cfv wcel wa caddc cof co cvv cmzpcl cdm elfvdm dmmzp syl6eleq adantr
    cmul mzpincl syl id mzpcl34 syl3anc simpld ) ACDEZFZBUEFZGZABHIJUEFZABRIJUE
    FZUHCKFZUECLEFZUHUIUJGUFUKUGUFCDMKACDNOPQZUHUKULUMCSTUHUAUEABCUBUCUD $.
    $( [4-Oct-2014] $)

  $( The pointwise product of two polynomial functions is a polynomial
     function.  See also ~ mzpmulmpt .  (Contributed by Stefan O'Rear,
     4-Oct-2014.) $)
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
       because ~ mzpproj is already expressed using maps-to notation.
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpconstmpt $p |- ( ( V e. _V /\ C e. ZZ ) -> ( x e. ( ZZ ^m V ) |-> C ) e.
        ( mzPoly ` V ) ) $=
      ( cvv wcel cz wa cmap cmpt csn cxp cmzp cfv fconstmpt mzpconst syl5eqelr
      co ) CDEBFEGAFCHQZBIRBJKCLMARBNBCOP $.
      $( [5-Oct-2014] $)

    $( Sum of polynomial functions is polynomial.  Maps-to version of
       ~ mzpadd .  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpaddmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e.
        ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A + B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel wa caddc cof wfn wf mzpf ffn syl cvv wceq
      ovex ofmpteq mp3an1 syl2an mzpadd eqeltrrd ) AEDFGZBHZDIJZKZAUHCHZUJKZLUI
      ULMNGZAUHBCMGHZUJUKUIUHOZULUHOZUNUOUAZUMUKUHEUIPUPUIDQUHEUIRSUMUHEULPUQUL
      DQUHEULRSUHTKUPUQUREDFUBAUHBCMTUCUDUEUIULDUFUG $.
      $( [5-Oct-2014] $)

    $( Product of polynomial functions is polynomial.  Maps-to version of
       ~ mzpmulmpt .  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
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
      $( The difference of two polynomial functions is polynomial.
         (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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

    $( Negation of a polynomial function.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    mzpnegmpt $p |- ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) -> ( x e. (
        ZZ ^m V ) |-> -u A ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel cneg cc0 cmin df-neg mpteq2i elfvdm dmmzp
      cvv cdm syl6eleq 0z mzpconstmpt sylancl mzpsubmpt mpancom syl5eqel ) ADCE
      FZBGZCHIZJZAUGBKZGAUGLBMFZGZUIAUGUKULBNOAUGLGUIJZUJUMUIJUJCRJLDJUNUJCHSRU
      HCHPQTUAALCUBUCALBCUDUEUF $.
      $( [11-Oct-2014] $)

    $( Raise a polynomial function to a (fixed) exponent.  (Contributed by
       Stefan O'Rear, 5-Oct-2014.) $)
    mzpexpmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ D e.
        NN0 ) ->
        ( x e. ( ZZ ^m V ) |-> ( A ^ D ) ) e. ( mzPoly ` V ) ) $=
      ( va vb wcel cz co cmpt cmzp cexp wi c1 wceq oveq2 mpteq2dv eleq1d imbi2d
      cc cn0 cmap cfv cv cc0 caddc weq wral wf wss mzpf zsscn sylancl eqid fmpt
      fss sylibr hbra1 wa ra4 imp syl mpteq2da cvv cdm elfvdm dmmzp syl6eleq 1z
      exp0 mzpconstmpt eqeltrd w3a cmul 3ad2ant2 simp1 ax-17 hban adantlr expp1
      simplr syl2anc simp3 simp2 mzpmulmpt 3exp a2d nn0ind impcom ) CUAGAHDUBIZ
      BJZDKUCZGZAWJBCLIZJZWLGZWMAWJBEUDZLIZJZWLGZMWMAWJBUELIZJZWLGZMWMAWJBFUDZL
      IZJZWLGZMWMAWJBXDNUFIZLIZJZWLGZMWMWPMEFCWQUEOZWTXCWMXLWSXBWLXLAWJWRXAWQUE
      BLPQRSEFUGZWTXGWMXMWSXFWLXMAWJWRXEWQXDBLPQRSWQXHOZWTXKWMXNWSXJWLXNAWJWRXI
      WQXHBLPQRSWQCOZWTWPWMXOWSWOWLXOAWJWRWNWQCBLPQRSWMXBAWJNJZWLWMBTGZAWJUHZXB
      XPOWMWJTWKUIZXRWMWJHWKUIHTUJXSWKDUKULWJHTWKUPUMAWJTBWKWKUNUOUQZXRAWJXANXQ
      AWJURZXRAUDWJGZUSXQXANOXRYBXQXQAWJUTVAZBVJVBVCVBWMDVDGNHGXPWLGWMDKVEVDWKD
      KVFVGVHVIANDVKUMVLXDUAGZWMXGXKYDWMXGXKYDWMXGVMZXJAWJXEBVNIZJZWLYEXRYDXJYG
      OWMYDXRXGXTVOYDWMXGVPXRYDUSZAWJXIYFXRYDAYAYDAVQVRYHYBUSXQYDXIYFOXRYBXQYDY
      CVSXRYDYBWABXDVTWBVCWBYEXGWMYGWLGYDWMXGWCYDWMXGWDAXEBDWEWBVLWFWGWHWI $.
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
    $( "Structural" induction to prove properties of all polynomial functions.
       (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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
       polynomials which are being substituted.  (Contributed by Stefan O'Rear,
       5-Oct-2014.) $)
    mzpsubst $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ A. y e. V G e. (
        mzPoly ` W ) ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( y e. V |-> ( G ` x ) ) ) ) e. ( mzPoly `
        W ) ) $=
      ( va vb vc cvv wcel cfv cz co cmpt wa wceq fveq1 eleq1d mpteq2dv cmzp w3a
      wral cmap cv simp1 cdm elfvdm dmmzp syl6eleq 3ad2ant2 simp3 simp2 csn cxp
      caddc cof cmul simpr simpll3 simpll2 wf mzpf ffvelrn sylan expcom ralimdv
      imp eqid fmpt sylib adantr wb zex elmapg sylancr mpbird syl21anc fvconst2
      vex syl mpteq2dva mzpconstmpt 3ad2antl1 eqeltrd csb fvex fvmpt simplr weq
      csbeq1 fveq1d ax-17 wel hbcsb1 csbeq1a cbvmpt fvmptg sylancl eqtrd simpl3
      hbfv wfn ax17el hbel rcla4 sylc dffn5v eqtr4d simp2l simp3l simp13 simp12
      ffn 3syl simplll simpllr ovex a1i simplrl simplrr fnfvof simp2r mzpaddmpt
      syl22anc simp3r syl2anc mzpmulmpt mzpindd syl31anc ) FJKZCEUALKZDFUALZKZB
      EUCZUBYKEJKZYOYLAMFUDNZBEAUEZDLZOZCLZOZYMKZYKYLYOUFYLYKYPYOYLEUAUGJCEUAUH
      UIUJUKYKYLYOULYKYLYOUMYKYPYOUBZAYQYTGUEZLZOZYMKAYQYTMEUDNZHUEZUNUOZLZOZYM
      KAYQYTIUUHUUIIUEZLZOZLZOZYMKAYQYTUUILZOZYMKZAYQYTUUMLZOZYMKZAYQYTUUIUUMUP
      UQNZLZOZYMKAYQYTUUIUUMURUQNZLZOZYMKUUCGCHIEUUDUUIMKZPZUULAYQUUIOZYMUVKAYQ
      UUKUUIUVKYRYQKZPZYTUUHKZUUKUUIQUVNUVMYOYPUVOUVKUVMUSYKYPYOUVJUVMUTYKYPYOU
      VJUVMVAUVMYOPZYPPZUVOEMYTVBZUVPUVRYPUVPYSMKZBEUCZUVRUVMYOUVTUVMYNUVSBEYNU
      VMUVSYNYQMDVBUVMUVSDFVCYQMYRDVDVEVFVGZVHBEMYSYTYTVIVJZVKVLUVQMJKZYPUVOUVR
      VMZVNUVPYPUSMEYTJJVOZVPVQZVRUUHUUIYTHVTZVSWAWBYKYPUVJUVLYMKYOAUUIFWCWDWEU
      UDUUIEKZPZUUQBUUIDWFZYMUWIUUQAYQYRUWJLZOZUWJUWIAYQUUPUWKUWIUVMPZUUPUUIYTL
      ZUWKUWMUVOUUPUWNQUWMUVMYOYPUVOUWIUVMUSYKYPYOUWHUVMUTYKYPYOUWHUVMVAUWFVRIY
      TUUNUWNUUHUUOUUIUUMYTRUUOVIUUIYTWGWHWAUWMUWHUWKJKUWNUWKQUUDUWHUVMWIYRUWJW
      GGUUIYRBUUEDWFZLZUWKEJYTGHWJZYRUWOUWJBUUEUUIDWKWLBGIEYSUWPUUMYSKGWMBIYRUW
      OBIUUEDGVTIGWNBWMWOIAWNBWMXBBGWJYRDUWOBUUEDWPWLWQWRWSWTWBUWIUWJYQXCZUWJUW
      LQUWIUWJYMKZYQMUWJVBUWRUWIUWHYOUWSUUDUWHUSYKYPYOUWHXAYNUWSBUUIEBGGUWJYMBG
      UUIDUWGGHBXDWOUUEYMKBWMXEBHWJDUWJYMBUUIDWPSXFXGZUWJFVCYQMUWJXNXOAYQUWJXHV
      KXIUWTWEUUDUUHMUUIVBZUUTPZUUHMUUMVBZUVCPZUBZUVFAYQUURUVAUPNZOZYMUXEUUIUUH
      XCZUUMUUHXCZYOYPUVFUXGQUXEUXAUXHUUDUXAUUTUXDXJUUHMUUIXNWAZUXEUXCUXIUUDUXB
      UXCUVCXKUUHMUUMXNWAZYKYPYOUXBUXDXLZYKYPYOUXBUXDXMZUXHUXIPZYOYPPZPZAYQUVEU
      XFUXPUVMPZUXHUXIUUHJKZUVOUVEUXFQUXHUXIUXOUVMXPZUXHUXIUXOUVMXQZUXRUXQMEUDX
      RXSZUXQUVOUVRUXQUVTUVRUXQUVMYOUVTUXPUVMUSUXNYOYPUVMXTUWAXGUWBVKUXQUWCYPUW
      DVNUXNYOYPUVMYAUWEVPVQZUUHUPUUIUUMJYTYBYEWBYEUXEUUTUVCUXGYMKUUDUXAUUTUXDY
      CZUUDUXBUXCUVCYFZAUURUVAFYDYGWEUXEUVIAYQUURUVAURNZOZYMUXEUXHUXIYOYPUVIUYF
      QUXJUXKUXLUXMUXPAYQUVHUYEUXQUXHUXIUXRUVOUVHUYEQUXSUXTUYAUYBUUHURUUIUUMJYT
      YBYEWBYEUXEUUTUVCUYFYMKUYCUYDAUURUVAFYHYGWEUUEUUJQZUUGUULYMUYGAYQUUFUUKYT
      UUEUUJRTSUUEUUOQZUUGUUQYMUYHAYQUUFUUPYTUUEUUORTSUWQUUGUUSYMUWQAYQUUFUURYT
      UUEUUIRTSGIWJZUUGUVBYMUYIAYQUUFUVAYTUUEUUMRTSUUEUVDQZUUGUVFYMUYJAYQUUFUVE
      YTUUEUVDRTSUUEUVGQZUUGUVIYMUYKAYQUUFUVHYTUUEUVGRTSUUECQZUUGUUBYMUYLAYQUUF
      UUAYTUUECRTSYIYJ $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d W x a b $.  $d F x a b $.  $d R x a b $.  $d V a x $.
    $( Simplified version of ~ mzpsubst to simply relabel variables in a
       polynomial.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzprename $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ R : V --> W ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( x o. R ) ) ) e. ( mzPoly ` W ) ) $=
      ( va vb cvv wcel cmzp cfv wf w3a cz cv cmpt wceq wa syl2anc mpteq2dva zex
      cmap co ccom simpr wb simpll elmapg sylancr mpbid simplr fcompt eqid fvex
      fveq1 fvmpt ad2antlr eqcomd eqtrd fveq2d 3adant2 simpl1 ffvelrn 3ad2antl3
      wral mzpproj ralrimiva mzpsubst syld3an3 eqeltrd ) EHIZCDJKIZDEBLZMZANEUB
      UCZAOZBUDZCKZPZAVOFDVPGVOFOZBKZGOZKZPZKZPZCKZPZEJKZVKVMVSWHQVLVKVMRZAVOVR
      WGWJVPVOIZRZVQWFCWLVQFDWAVPKZPZWFWLENVPLZVMVQWNQWLWKWOWJWKUEWLNHIVKWKWOUF
      UAVKVMWKUGNEVPHHUHUIUJVKVMWKUKFVPBDENULSWLFDWMWEWLVTDIZRWEWMWKWEWMQWJWPGV
      PWCWMVOWDWAWBVPUOWDUMWAVPUNUPUQURTUSUTTVAVKVLVMWDWIIZFDVEWHWIIVNWQFDVNWPR
      VKWAEIZWQVKVLVMWPVBVMVKWPWRVLDEVTBVCVDGEWAVFSVGAFCWDDEVHVIVJ $.
      $( [5-Oct-2014] $)
  $}

  ${
    $d W x $.  $d F x $.  $d V x $.
    $( A polynomial is a polynomial over all larger index sets.  (Contributed
       by Stefan O'Rear, 5-Oct-2014.) $)
    mzpresrename $p |- ( ( W e. _V /\ V C_ W /\ F e. ( mzPoly ` V ) ) -> ( x e.
        ( ZZ ^m W ) |-> ( F ` ( x |` V ) ) ) e. ( mzPoly ` W ) ) $=
      ( cvv wcel wss cmzp cfv w3a cz cmap co cv cres cmpt cid ccom wa wf elmapi
      wrel wceq 3ad2antl1 frel coires1 3syl eqcomd fveq2d mpteq2dva simp1 simp3
      wf1o f1oi f1of ax-mp fss mpan 3ad2ant2 mzprename syl3anc eqeltrd ) DEFZCD
      GZBCHIFZJZAKDLMZANZCOZBIZPAVGVHQCOZRZBIZPZDHIZVFAVGVJVMVFVHVGFZSZVIVLBVQV
      LVIVQDKVHTZVHUBVLVIUCVCVDVPVRVEVHKDUAUDDKVHUEVHCUFUGUHUIUJVFVCVECDVKTZVNV
      OFVCVDVEUKVCVDVEULVDVCVSVECCVKTZVDVSCCVKUMVTCUNCCVKUOUPCCDVKUQURUSAVKBCDU
      TVAVB $.
      $( [5-Oct-2014] $)
  $}


  ${
    $d A a b d e f g h i j k l $.  $d B a b c d e f g h i j k l $.
    mzpcompact2lem.i $e |- B e. _V $.
    $( Lemma for ~ mzpcompact2 . $)
    mzpcompact2lem $p |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly
        ` a ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) )
        $=
      ( vd cmzp cfv wcel cv cz co cmpt wceq wa wrex cfn c0 anbi2d ve vf vg cmap
      vh vi vj vk vl wss cres wtru tru csn cxp caddc cof cmul 0fin cvv mzpconst
      0ex 0ss a1i simpr elmapssres syl3anc vex fvconst2 syl mpteq2dva fconstmpt
      syl6reqr fveq1 mpteq2dv eqeq2d rcla4ev syl12anc fveq2 sseq1 reseq2 fveq2d
      mpan anbi12d rexeqbidv sylancr snfi snex snid mzpproj mp2an snssi cbvmptv
      adantl simpl snssd eqid fvex fvmpt fvres ax-mp syl6req syl5eq w3a simplll
      wf cun simprll unfi syl2anc unex ssun1 simpllr mzpresrename ssun2 simprlr
      mzpaddmpt simplr wfn ovex mzpf ffn 3syl ofmpteq zex elmap oveq12d resabs1
      wi reseq1 fveq2i oveq12i eqtrd eqeq1d rexbidv 2rexbidv weq cbvrexv syl6bb
      eqeq1 simprr unssd biimpi fssres syl2anr sylibr adantlrr adantrrr simplrr
      mzpmulmpt simprrr mpbird r19.40 exp32 rexlimdvv ex rexlimivv imp ad2ant2l
      3adant1 simpld simprd mzpindd eqeq2i anbi2i 2rexbii sylib ) ABHIZJZCKZBUJ
      ZAGLBUDMZGKZUVJUKZDKZIZNZOZPZDUVJHIZQCRQZUVKAEUVLEKZUVJUKZUVOIZNZOZPZDUVT
      QCRQULUVIUWAUMULUVKUAKZUVQOZPZDUVTQCRQZUVKUVLUBKZUNZUOZUVQOZPZDUVTQZCRQZU
      VKUCUVLUWLUCKZIZNZUVQOZPZDUVTQZCRQZUEKZBUJZUWLGUVLUVMUXFUKZUFKZIZNZOZPZUF
      UXFHIZQZUERQZUGKZBUJZUWSGUVLUVMUXQUKZUHKZIZNZOZPZUHUXQHIZQZUGRQZUVKUWLUWS
      UPUQZMZUVQOZPZDUVTQZCRQZUVKUWLUWSURUQZMZUVQOZPZDUVTQZCRQZUWAUAAUBUCBUWLLJ
      ZUWRULUYTSRJSBUJZUWNGUVLUVMSUKZUVOIZNZOZPZDSHIZQZUWRUSUYTLSUDMZUWMUOZVUGJ
      ZVUAUWNGUVLVUBVUJIZNZOZVUHSUTJUYTVUKVBUWLSVAWCVUAUYTBVCZVDUYTVUMGUVLUWLNU
      WNUYTGUVLVULUWLUYTUVMUVLJZPZVUBVUIJZVULUWLOVUQVUPVUABUTJZVURUYTVUPVEVUAVU
      QVUOVDVUSVUQFVDUVMLBSVFVGVUIUWLVUBUBVHZVIVJVKGUVLUWLVLVMVUFVUAVUNPDVUJVUG
      UVOVUJOZVUEVUNVUAVVAVUDVUMUWNVVAGUVLVUCVULVUBUVOVUJVNVOVPTVQVRUWQVUHCSRUV
      JSOZUWPVUFDUVTVUGUVJSHVSVVBUVKVUAUWOVUEUVJSBVTVVBUVQVUDUWNVVBGUVLUVPVUCVV
      BUVNVUBUVOUVJSUVMWAWBVOVPWDWEVQWFWNUWLBJZUXEULVVCUWMRJUWMBUJZUXAGUVLUVMUW
      MUKZUVOIZNZOZPZDUWMHIZQZUXEUWLWGVVCUCLUWMUDMZUWTNZVVJJZVVDUXAGUVLVVEVVMIZ
      NZOZVVKVVNVVCUWMUTJUWLUWMJZVVNUWLWHUWLVUTWIZUCUWMUWLWJWKVDUWLBWLVVCUXAGUV
      LUWLUVMIZNVVPUCGUVLUWTVVTUWLUWSUVMVNWMVVCGUVLVVTVVOVVCVUPPZVVOUWLVVEIZVVT
      VWAVVEVVLJZVVOVWBOVWAVUPVVDVUSVWCVVCVUPVEVWAUWLBVVCVUPWOWPVUSVWAFVDUVMLBU
      WMVFVGUCVVEUWTVWBVVLVVMUWLUWSVVEVNVVMWQUWLVVEWRWSVJVVRVWBVVTOVVSUWLUWMUVM
      WTXAXBVKXCVVIVVDVVQPDVVMVVJUVOVVMOZVVHVVQVVDVWDVVGVVPUXAVWDGUVLVVFVVOVVEU
      VOVVMVNVOVPTVQVRUXDVVKCUWMRUVJUWMOZUXCVVIDUVTVVJUVJUWMHVSVWEUVKVVDUXBVVHU
      VJUWMBVTVWEUVQVVGUXAVWEGUVLUVPVVFVWEUVNVVEUVOUVJUWMUVMWAWBVOVPWDWEVQWFWNU
      LUVLLUWLXFZUXPPZUVLLUWSXFZUYGPZXDZUYMUYSVWGVWIUYMUYSPZULUXPUYGVWKVWFVWHUX
      PUYGVWKUXMUYGVWKYIZUEUFRUXNUXFRJZUXIUXNJZPZUXMVWLVWOUXMPZUYDVWKUGUHRUYEVW
      PUXQRJZUXTUYEJZPZUYDVWKVWPVWSUYDPZPZUYLUYRPZCRQZVWKVXAVXCUVKUXKUYBUYHMZUV
      QOZPZDUVTQZUVKUXKUYBUYNMZUVQOZPZDUVTQZPZCRQZVWPVWSUXRVXMUYCVWOUXGVWSUXRPZ
      VXMUXLVWOUXGPZVXNPZUXFUXQXGZRJZVXQBUJZVXDGUVLUVMVXQUKZUVOIZNZOZPZDVXQHIZQ
      ZVXSVXHVYBOZPZDVYEQZVXMVXPVWMVWQVXRVWMVWNUXGVXNXEVXOVWQVWRUXRXHUXFUXQXIXJ
      VXPUILVXQUDMZUIKZUXFUKZUXIIZVYKUXQUKZUXTIZUPMZNZVYEJZVXSVXDGUVLVXTVYQIZNZ
      OZVYFVXPUIVYJVYMNVYEJZUIVYJVYONVYEJZVYRVXPVXQUTJZUXFVXQUJZVWNWUBWUDVXPUXF
      UXQUEVHUGVHXKZVDZWUEVXPUXFUXQXLZVDVWMVWNUXGVXNXMZUIUXIUXFVXQXNVGZVXPWUDUX
      QVXQUJZVWRWUCWUGWUKVXPUXQUXFXOZVDVXOVWQVWRUXRXPZUIUXTUXQVXQXNVGZUIVYMVYOV
      XQXQXJVXPUXFUXQBVWOUXGVXNXRZVXOVWSUXRUUAZUUBZVXPVXDGUVLUXJUYAUPMZNZVYTVXP
      UVLUTJZUXKUVLXSZUYBUVLXSZVXDWUSOWUTVXPLBUDXTVDZVXPUXKUVHJZUVLLUXKXFWVAVXP
      VUSUXGVWNWVDVUSVXPFVDZWUOWUIGUXIUXFBXNVGUXKBYAUVLLUXKYBYCZVXPUYBUVHJZUVLL
      UYBXFWVBVXPVUSUXRVWRWVGWVEWUPWUMGUXTUXQBXNVGUYBBYAUVLLUYBYBYCZGUVLUXJUYAU
      PUTYDVGVXPGUVLWURVYSVXPVUPPZVYSVXTUXFUKZUXIIZVXTUXQUKZUXTIZUPMZWURWVIVXTV
      YJJZVYSWVNOWVIVXQLVXTXFZWVOVUPBLUVMXFZVXSWVPVXPVUPWVQLBUVMYEFYFUUCWUQBLVX
      QUVMUUDUUELVXQVXTYEWUFYFUUFZUIVXTVYPWVNVYJVYQVYKVXTOZVYMWVKVYOWVMUPWVSVYL
      WVJUXIVYKVXTUXFYJWBZWVSVYNWVLUXTVYKVXTUXQYJWBZYGVYQWQWVKWVMUPXTWSVJWVKUXJ
      WVMUYAUPWVJUXHUXIWUEWVJUXHOWUHUVMUXFVXQYHXAYKZWVLUXSUXTWUKWVLUXSOWULUVMUX
      QVXQYHXAYKZYLXBVKYMVYDVXSWUAPDVYQVYEUVOVYQOZVYCWUAVXSWWDVYBVYTVXDWWDGUVLV
      YAVYSVXTUVOVYQVNVOVPTVQVRVXPUIVYJVYMVYOURMZNZVYEJZVXSVXHGUVLVXTWWFIZNZOZV
      YIVXPWUBWUCWWGWUJWUNUIVYMVYOVXQUUJXJWUQVXPVXHGUVLUXJUYAURMZNZWWIVXPWUTWVA
      WVBVXHWWLOWVCWVFWVHGUVLUXJUYAURUTYDVGVXPGUVLWWKWWHWVIWWHWVKWVMURMZWWKWVIW
      VOWWHWWMOWVRUIVXTWWEWWMVYJWWFWVSVYMWVKVYOWVMURWVTWWAYGWWFWQWVKWVMURXTWSVJ
      WVKUXJWVMUYAURWWBWWCYLXBVKYMVYHVXSWWJPDWWFVYEUVOWWFOZVYGWWJVXSWWNVYBWWIVX
      HWWNGUVLVYAWWHVXTUVOWWFVNVOVPTVQVRVXLVYFVYIPCVXQRUVJVXQOZVXGVYFVXKVYIWWOV
      XFVYDDUVTVYEUVJVXQHVSZWWOUVKVXSVXEVYCUVJVXQBVTZWWOUVQVYBVXDWWOGUVLUVPVYAW
      WOUVNVXTUVOUVJVXQUVMWAWBVOZVPWDWEWWOVXJVYHDUVTVYEWWPWWOUVKVXSVXIVYGWWQWWO
      UVQVYBVXHWWRVPWDWEWDVQVRUUGUUHVXAVXBVXLCRVXAUYLVXGUYRVXKVXAUYKVXFDUVTVXAU
      YJVXEUVKVXAUYIVXDUVQVXAUWLUXKUWSUYBUYHVWOUXGUXLVWTUUIZVWPVWSUXRUYCUUKZYGY
      NTYOVXAUYQVXJDUVTVXAUYPVXIUVKVXAUYOVXHUVQVXAUWLUXKUWSUYBUYNWWSWWTYGYNTYOW
      DYOUULUYLUYRCRUUMVJUUNUUOUUPUUQUURUUSUUTZUVAVWJUYMUYSWXAUVBUWHUWNOZUWJUWP
      CDRUVTWXBUWIUWOUVKUWHUWNUVQYTTYPUWHUXAOZUWJUXCCDRUVTWXCUWIUXBUVKUWHUXAUVQ
      YTTYPUAUBYQZUWKUVKUWLUVQOZPZDUVTQZCRQUXPWXDUWJWXFCDRUVTWXDUWIWXEUVKUWHUWL
      UVQYTTYPWXGUXOCUERCUEYQZWXGUXGUWLGUVLUXHUVOIZNZOZPZDUXNQUXOWXHWXFWXLDUVTU
      XNUVJUXFHVSWXHUVKUXGWXEWXKUVJUXFBVTWXHUVQWXJUWLWXHGUVLUVPWXIWXHUVNUXHUVOU
      VJUXFUVMWAWBVOVPWDWEWXLUXMDUFUXNDUFYQZWXKUXLUXGWXMWXJUXKUWLWXMGUVLWXIUXJU
      XHUVOUXIVNVOVPTYRYSYRYSUAUCYQZUWKUVKUWSUVQOZPZDUVTQZCRQUYGWXNUWJWXPCDRUVT
      WXNUWIWXOUVKUWHUWSUVQYTTYPWXQUYFCUGRCUGYQZWXQUXRUWSGUVLUXSUVOIZNZOZPZDUYE
      QUYFWXRWXPWYBDUVTUYEUVJUXQHVSWXRUVKUXRWXOWYAUVJUXQBVTWXRUVQWXTUWSWXRGUVLU
      VPWXSWXRUVNUXSUVOUVJUXQUVMWAWBVOVPWDWEWYBUYDDUHUYEDUHYQZWYAUYCUXRWYCWXTUY
      BUWSWYCGUVLWXSUYAUXSUVOUXTVNVOVPTYRYSYRYSUWHUYIOZUWJUYKCDRUVTWYDUWIUYJUVK
      UWHUYIUVQYTTYPUWHUYOOZUWJUYQCDRUVTWYEUWIUYPUVKUWHUYOUVQYTTYPUWHAOZUWJUVSC
      DRUVTWYFUWIUVRUVKUWHAUVQYTTYPUVCWCUVSUWGCDRUVTUVRUWFUVKUVQUWEAGEUVLUVPUWD
      GEYQUVNUWCUVOUVMUWBUVJYJWBWMUVDUVEUVFUVG $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b d $.  $d B a b c d $.
    $( Polynomials are finitary objects and can only reference a finite number
       of variables, even if the index set is infinite.  Thus, every polynomial
       can be expressed as a (uniquely minimal, although we do not prove that)
       polynomial on a finite number of variables, which is then extended by
       adding an arbitrary set of ignored variables.  (Contributed by Stefan
       O'Rear, 9-Oct-2014.) $)
    mzpcompact2 $p |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly ` a
        ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) ) $=
      ( vd cvv wcel cmzp cfv cv wss cz cmap co cmpt wceq wa wrex cfn cdm elfvdm
      cres dmmzp syl6eleq wi fveq2 eleq2d sseq2 oveq2 mpteq1 syl eqeq2d anbi12d
      2rexbidv imbi12d vex mzpcompact2lem vtoclg mpcom ) BGHABIJZHZCKZBLZAEMBNO
      ZEKVCUCDKJZPZQZRZDVCIJZSCTSZVBBIUAGABIUBUDUEAFKZIJZHZVCVLLZAEMVLNOZVFPZQZ
      RZDVJSCTSZUFVBVKUFFBGVLBQZVNVBVTVKWAVMVAAVLBIUGUHWAVSVICDTVJWAVOVDVRVHVLB
      VCUIWAVQVGAWAVPVEQVQVGQVLBMNUJEVPVEVFUKULUMUNUOUPAVLCDEFUQURUSUT $.
      $( [9-Oct-2014] $)
  $}
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Miscellanea for Diophantine sets 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Two real numbers are equal to 0 iff their Euclidean norm is.  Closed
     theorem of ~ sumsqeq0 .  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
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
     with ~ coundi and ~ coundir to prune meaningless terms in the result.
     (Contributed by Stefan O'Rear, 8-Oct-2014.) $)
  coeq0 $p |- ( ( A o. B ) = (/) <-> ( dom A i^i ran B ) = (/) ) $=
    ( ccom c0 wceq crn cres cdm wrel wb relco relrn0 ax-mp eqeq1i relres reldm0
    cin rnco dmres incom eqtri 3bitr3i 3bitri ) ABCZDEZUDFZDEZABFZGZFZDEZAHZUHQ
    ZDEZUDIUEUGJABKUDLMUFUJDABRNUIDEZUIHZDEZUKUNUIIZUOUQJAUHOZUIPMURUOUKJUSUILM
    UPUMDUPUHULQUMAUHSUHULTUANUBUC $.
    $( [8-Oct-2014] $)

  $( ~ coeq0 but without explicitly introducing domain and range symbols.
     (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
  coeq0i $p |- ( ( A : C --> D /\ B : E --> F /\ ( C i^i F ) = (/) ) ->
      ( A o. B ) = (/) ) $=
    ( wf cin c0 wceq w3a cdm crn ccom wss frn 3ad2ant2 sslin syl fdm ineq1d ss0
    3ad2ant1 simp3 eqtrd sseqtrd coeq0 sylibr ) CDAGZEFBGZCFHZIJZKZALZBMZHZIJZA
    BNIJUMUPIOUQUMUPUNFHZIUMUOFOZUPUROUJUIUSULEFBPQUOFUNRSUMURUKIUMUNCFUIUJUNCJ
    ULCDATUCUAUIUJULUDUEUFUPUBSABUGUH $.
    $( [16-Oct-2014] $)

  $( Split a finite 1-based set of integers in the middle, allowing either end
     to be empty ( ` ( 1 ... 0 ) ` ).  (Contributed by Stefan O'Rear,
     8-Oct-2014.) $)
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
       Extension of ~ isinf from finite ordinals to all finite sets.
       (Contributed by Stefan O'Rear, 8-Oct-2014.) $)
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
    $( Initial expression of Diophantine property of a set.  (Contributed by
       Stefan O'Rear, 5-Oct-2014.) $)
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
    $( Condition for a set to be Diophantine (unpacking existential quantifier)
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
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

  ${
    $d S a b c d $.  $d T a b c d $.  $d M a b c d $.  $d O a b c d $.
    $d P b c d $.
    $( Renaming and adding unused witness variables does not change the
       Diophantine set coded by a polynomial.  (Contributed by Stefan O'Rear,
       7-Oct-2014.) $)
    diophrw $p |- ( ( S e. _V /\ M : T -1-1-> S /\ ( M |` O ) = ( _I |` O ) )
        -> { a | E. b e. ( NN0 ^m S ) ( a = ( b |` O ) /\ ( ( d e. ( ZZ ^m S )
        |-> ( P ` ( d o. M ) ) ) ` b ) = 0 ) } = { a | E. c e. ( NN0 ^m T ) ( a
        = ( c |` O ) /\ ( P ` c ) = 0 ) } ) $=
      ( cvv wcel cres wceq cz ccom cc0 cn0 wf a1i c0 wf1 cid w3a cv cmap co cfv
      cmpt wa wrex simpr nn0ex simp1 adantr elmapg sylancr mpbid simp2 ad2antrr
      f1f syl fco syl2anc f1dmex mpbird simprl resco simpll3 coeq2d wrel simplr
      wb simpll1 frel coires1 3syl 3eqtrd eqtr4d wss oveq2 sseq12d nn0ssz mapss
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
      WDUXGUWPVKZUXIUXSUVSUXTULUVSUVTUWCUXGUWPVMZUYBUPUQBQUWFVNUWFEVOVPVQVRUXIU
      WNUXNPUXIUWFUWIKUWNUXNMUXIUWQUWIUWFUXIUVSUWQUWIVSZUYJQUWEUEUFZNUWEUEUFZVS
      ZUYKFBJUWEBMUYLUWQUYMUWIUWEBQUEVTUWEBNUEVTWAQNVSZUYNWBQNUWEWDFWPWCWEWFVAU
      YIWGIUWFUWLUXNUWIUWMIGWQUWKUXJAUWJUWFDWHWIUWMWJZUXJAWKWLVAUXHUWHUWOWMWNUX
      DUXMUXOUIHUXJUXEUWSUXJMZUXAUXMUXCUXOUYQUWTUXLUWEUWSUXJEWOWRUYQUXBUXNPUWSU
      XJAXHWSWTXAXBXCXDUWDUXDUWRHUXEUWDUWSUXEKZUIZUXDUWRUYSUXDUIZUWSDXEZOZBDXFZ
      XGZPXIZXJZXKZUWQKZUWEVUGELZMZVUGUWMUGZPMZUWRUYTVUHBQVUGRZUYTVUCVUDXKZQVUE
      XKZVUGRZVUMUYTVUCQVUBRZVUDVUEVUFRZVUCVUDXLZTMZVUPUYTCQUWSRZVUCCVUARZVUQUY
      SVVAUXDUYSUYRVVAUWDUYRUKUYSUXSUYEUYRVVAVLULUWDUYEUYRUYFUNQCUWSJJUOUPUQZUN
      ZUYTUVTVUCCVUAXMVVBUWDUVTUYRUXDUYCUSZCBDXNVUCCVUAYBVPZVUCCQUWSVUAVBVCVURU
      YTVUDPPNXOXPZXQSZVUTUYTVUCBXRZSZVUCVUDQVUEVUBVUFXSXTUYTVUNVUOBQVUGUYTVUCB
      VSZVUNBMUWDVVKUYRUXDUWDUVTUXRVVKUYCUYDCBDYAVPUSVUCBYCYDZVUOQMZUYTVUEQVSZV
      VMPQKVVNYEPQYFWEVUEQYGYHSYIUQUWDVUHVUMVLZUYRUXDUWDUXSUVSVVOULUYAQBVUGJJUO
      UPUSVEUYTUWEUWTVUIUYSUXAUXCVFUYSUWTVUIMUXDUYSVUIVUBELZVUFELZXKZUWTTXKZUWT
      VUIVVRMUYSVUBVUFEYJSUYSVVPUWTVVQTUYSVVPUWSVUAELZOZUWSUWBOZUWTVVPVWAMUYSUW
      SVUAEVGSUYSVVTUWBUWSUYSUWAXEZUWBXEZVVTUWBUYSUWAUWBUVSUVTUWCUYRYKZYNUYSVWC
      VUADEYLZLZVVTUYSUVTVUAYMZVWCVWGMUVSUVTUWCUYRYOUVTUXRVWHCBDUUAUUBEDUUCVPUY
      SVWFEVUAUYSVWFUWAXFZUWBXFZEVWFVWIMUYSDEUUDSUYSUWAUWBVWEUUEZVWJEMUYSEUUFSZ
      VQUUGYPVWDUWBMUYSEUUHSUUIVIUYSVVAUWSVJVWBUWTMVVCCQUWSVNUWSEVOVPVQUYSVVQYQ
      ZTMZVVQTMZUYSVWMEVUFYQZXLZTVUFEUUJUYSVWQEVUDXLZTVWPVUDEVUETUUPVWPVUDMPVVG
      UUKVUDVUEUULWEZUUMUYSEBXLZVUCVSVWRTMUYSVWTEVUCEBUUNUYSEVWIVUCUYSVWIVWJEVW
      KVWLUUOUYSUWADVSZVWIVUCVSVXAUYSDEUVGSUWADUUQVAUURUUSEBVUCUUTYDYRYRVVQVJVW
      OVWNVLVUFEUVAVVQUVBWEUVCYSVVSUWTMUYSUWTYTSUVDUNYPUYTVUKVUGDOZAUGZUXBPUYTV
      UGUWIKZVUKVXCMUYTVXDBNVUGRZUYTVUNNVUEXKZVUGRZVXEUYTVUCNVUBRZVURVUTVXGUYTC
      NUWSRZVVBVXHUYSVXIUXDUYSVVAUYOVXIVVCWBCQNUWSUVEUVFUNVVFVUCCNUWSVUAVBVCVVH
      VVJVUCVUDNVUEVUBVUFXSXTUYTVUNVXFBNVUGVVLVXFNMZUYTVUENVSZVXJPNKVXKXOPNYFWE
      VUENYGYHSYIUQUWDVXDVXEVLZUYRUXDUWDNJKUVSVXLWDUYANBVUGJJUOUPUSVEIVUGUWLVXC
      UWIUWMUWJVUGMUWKVXBAUWJVUGDWHWIUYPVXBAWKWLVAUYTVXBUWSAUYTVXBVUBDOZVUFDOZX
      KZUWSUBCLZOZTXKZUWSVXBVXOMUYTVUBVUFDUVHSUYTVXMVXQVXNTUYTVXMUWSVUADOZOZVXQ
      UWSVUADUVIUYTUVTVXTVXQMVVEUVTVXSVXPUWSCBDUVJVIVAYRVXNTMZUYTVYAVWPVUCXLZTM
      VYBVUDVUCXLVUSTVWPVUDVUCVWSUVKVUDVUCUVLVVIUVMVUFDUVNUVOSYSUYTVXRVXQUWSVXQ
      YTUYTVVAVXQUWSMVVDCQUWSUVPVAYRVQWIUYSUXAUXCWMVQUWPVUJVULUIGVUGUWQUWFVUGMZ
      UWHVUJUWOVULVYCUWGVUIUWEUWFVUGEWOWRVYCUWNVUKPUWFVUGUWMXHWSWTXAXBXCXDUVQUV
      R $.
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
       drawn from any set whatsoever, via ~ mzpcompact2 .  (Contributed by
       Stefan O'Rear, 8-Oct-2014.) $)
    eldioph2 $p |- ( ( N e. NN0 /\ ( S e. _V /\ ( 1 ... N ) C_ S ) /\ P e. (
        mzPoly ` S ) ) ->
        { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0
        ) } e. ( Dioph ` N ) ) $=
      ( va ve wcel cvv co wss wa cfv cv cres wceq wrex cfn cc0 ccom vb vc vd vg
      vh cn0 c1 cfz cmzp w3a cz cmap cmpt cab cdioph mzpcompact2 3ad2ant3 fveq1
      eqeq1d anbi2d rexbidv abbidv ad2antll wi cun wf1o cid cuz simplll simplrl
      fzfi unfi sylancl a1i eldioph2lem1 syl3anc ccnv wfun wrel elmapfun funrel
      ssun2 coires1 eqcomd 3syl adantl f1ococnv2 ad2antrl reseq1d ssun1 resabs1
      ax-mp syl6req resco syl6eq adantr coeq2d eqcomi 3eqtrd fveq2d ovex simprl
      coass wf ad2antrr ad3antrrr simpr wf1 f1of1 simprr unssd f1ss syl2anc f1f
      syl mapco2g syl22anc coeq1 eqid fvex fvmpt eqtr4d mpteq2dva diophrw eqtrd
      fveq1d simpll simplrr f1ocnv f1of mzprename eldioph eqeltrd ex rexlimdvva
      fssres mpd exp31 3adant3 imp31 adantrr ) EUFHZDIHZUGEUHJZDKZLZCDUIMHZUJZF
      NZDKZCGUKDULJZGNZUUIOZUANZMZUMZPZLZUAUUIUIMZQFRQZBNZANZUUDOPZUVBCMZSPZLZA
      UFDULJZQZBUNZEUOMZHZUUGUUBUUTUUFCDFUAGUPUQUUHUURUVKFUARUUSUUHUUIRHZUUNUUS
      HZLZLZUURUVKUVOUURLUVIUVCUVBUUPMZSPZLZAUVGQZBUNZUVJUUQUVIUVTPUVOUUJUUQUVH
      UVSBUUQUVFUVRAUVGUUQUVEUVQUVCUUQUVDUVPSUVBCUUPURUSUTVAVBVCUVOUUJUVTUVJHZU
      UQUUHUVNUUJUWAUUBUUFUVNUUJUWAVDVDUUGUUBUUFLZUVNUUJUWAUWBUVNLZUUJLZUGUBNZU
      HJZUUIUUDVEZUCNZVFZUWHUUDOVGUUDOPZLZUCIQUBEVHMZQZUWAUWDUUBUWGRHZUUDUWGKZU
      WMUUBUUFUVNUUJVIUWDUVLUUDRHUWNUWBUVLUVMUUJVJUGEVKUUIUUDVLVMUWOUWDUUDUUIWB
      VNUWGUCEUBVOVPUWDUWKUWAUBUCUWLIUWDUWEUWLHZUWHIHZLZLZUWKUWAUWSUWKLZUVTUVAU
      DNZUUDOPUXAUEUKUWFULJZUENZUWHVQZUUIOZTZUUNMZUMZMSPLUDUFUWFULJQBUNZUVJUWTU
      VTUVCUVBGUUKUULUWHTZUXHMZUMZMZSPZLZAUVGQZBUNZUXIUWTUVSUXPBUWTUVRUXOAUVGUW
      TUVQUXNUVCUWTUVPUXMSUWTUVBUUPUXLUWTGUUKUUOUXKUWTUULUUKHZLZUUOUXJUXETZUUNM
      ZUXKUXSUUMUXTUUNUXSUUMUULVGUUIOZTZUULUWHUXETZTZUXTUXRUUMUYCPZUWTUXRUULVRU
      ULVSZUYFUULUKDVTUULWAUYGUYCUUMUULUUIWCWDWEWFUXSUYBUYDUULUWTUYBUYDPUXRUWTU
      YBUWHUXDTZUUIOZUYDUWTUYIVGUWGOZUUIOZUYBUWTUYHUYJUUIUWIUYHUYJPUWSUWJUWFUWG
      UWHWGWHWIUUIUWGKZUYKUYBPUUIUUDWJZVGUUIUWGWKWLWMUWHUXDUUIWNWOWPWQUYEUXTPUX
      SUXTUYEUULUWHUXEXCWRVNWSWTUXSUXJUXBHZUXKUYAPUXSUWFIHZUUCUXRUWFDUWHXDZUYNU
      YOUXSUGUWEUHXAZVNUWDUUCUWRUWKUXRUWBUUCUVNUUJUUBUUCUUEXBXEXFUWTUXRXGUWTUYP
      UXRUWTUWFDUWHXHZUYPUWTUWFUWGUWHXHZUWGDKZUYRUWIUYSUWSUWJUWFUWGUWHXIWHUWDUY
      TUWRUWKUWDUUIUUDDUWCUUJXGUWBUUEUVNUUJUUBUUCUUEXJXEXKXEUWFUWGDUWHXLXMZUWFD
      UWHXNXOWPUULUKDUWHUWFXPXQUEUXJUXGUYAUXBUXHUXCUXJPUXFUXTUUNUXCUXJUXEXRWTUX
      HXSUXTUUNXTYAXOYBYCYFUSUTVAVBUWTUUCUYRUWJUXQUXIPUWCUUCUUJUWRUWKUUBUUCUUEU
      VNVJXFVUAUWSUWIUWJXJUXHDUWFUWHUUDBAUDGYDVPYEUWTUUBUWPUXHUWFUIMHZUXIUVJHUW
      CUUBUUJUWRUWKUUBUUFUVNYGXFUWDUWPUWQUWKVJUWTUYOUVMUUIUWFUXEXDZVUBUYOUWTUYQ
      VNUWDUVMUWRUWKUWBUVLUVMUUJYHXEUWIVUCUWSUWJUWIUWGUWFUXDXDZUYLVUCUWIUWGUWFU
      XDVFVUDUWFUWGUWHYIUWGUWFUXDYJXOUYMUWGUWFUUIUXDYPVMWHUEUXEUUNUUIUWFYKVPUDB
      UXHUWEEYLVPYMYNYOYQYRYSYTUUAYMYNYOYQ $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d A a b p $.  $d N a b c d e u t p $.  $d S a b c d e u t p $.
    $( While Diophantine sets were defined to have a finite number of witness
       variables consequtively following the observable variables, this is not
       necessary; they can equivalently be taken to use any witness set
       ` ( S \ ( 1 ... N ) ) ` .  For instance, in ~ diophin we use this to
       take the two input sets to have disjoint witness sets.  (Contributed by
       Stefan O'Rear, 8-Oct-2014.) $)
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
    $( Remove antecedent on ` B ` from Diophantine set contructors.
       (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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
       variables and will be easier to use than ~ eldiophb in most cases.
       (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    eldioph3b $p |- ( A e. ( Dioph ` N ) <-> ( N e. NN0 /\
        E. p e. ( mzPoly ` NN ) A = { t | E. u e. ( NN0 ^m NN ) ( t = ( u |` (
        1 ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( cdioph cfv wcel cn0 cv c1 co wceq wa cn wrex cvv wb cfn com cfz cc0 cab
      cres cmap cmzp eldiophelnn0 nnex wss ominf cen wbr omex nnenom enfi mp2an
      wn mtbir elfznn ssriv eldioph2b mpanr12 mpan2 biadan2 ) CDFGHZDIHZCBJAJZK
      DUALZUDMVGEJZGUBMNAIOUELPBUCMEOUFGPZCDUGVFOQHZVEVJRZUHVFVKNOSHZUQVHOUIVLV
      MTSHZUJTQHOTUKULVMVNRUMUNOTQUOUPUREVHOVIDUSUTABCODEVAVBVCVD $.
      $( [10-Oct-2014] $)
  $}

  $( could maybe shorten a LOT of these with a canned substitution huh? $)
  ${
    $d A a b p t u $.  $d N a b p t u $.  $d P a b p t u $.
    $( Inference version of ~ eldioph3b with quantifier expanded.  (Contributed
       by Stefan O'Rear, 10-Oct-2014.) $)
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
     union of three functions with pairwise disjoint domains.  (Contributed by
     Stefan O'Rear, 9-Oct-2014.) $)
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
     function.  (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
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
     component can be recovered by restriction.  (Contributed by Stefan O'Rear,
     9-Oct-2014.) $)
  fresaunres2 $p |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = (
      G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G ) $=
    ( wf cin cres wceq cun cdif wfn ffn resundir wss ax-mp c0 cdm eqtri syl5eq
    w3a id resasplit syl3an reseq1d inss2 resabs2 uneq12i ineq2i disjdif ineq1i
    dmres inass inss1 0ss eqssi 3eqtr3i wrel wb relres reldm0 mpbir difss simp3
    uneq2i uneq1d wa uncom un0 resundi incom uneq1i inundif reseq2i fnresdm syl
    adantl syl5eqr 3adant3 eqtrd ) ACDFZBCEFZDABGZHZEWCHZIZUAZDEJZBHWDDABKZHZEB
    AKZHZJZJZBHZEWGWHWNBWADALWBEBLZWFWFWHWNIACDMBCEMZWFUBABDEUCUDUEWGWOWDBHZWMB
    HZJZEWDWMBNWGWTWDWJBHZWLBHZJZJZEWRWDWSXCWCBOWRWDIABUFDWCBUGPWJWLBNUHWGXDWDQ
    WLJZJZEXCXEWDXAQXBWLXAQIZXARZQIZXHBWJRZGZQWJBULXKBWIDRZGZGZQXJXMBDWIULUIBWI
    GZXLGQXLGZXNQXOQXLBAUJUKBWIXLUMXPQQXLUNXPUOUPUQSSXAURXGXIUSWJBUTXAVAPVBWKBO
    XBWLIBAVCEWKBUGPUHVEWGXFWEXEJZEWGWDWEXEWAWBWFVDVFWAWBXQEIWFWAWBVGZXQWEWLJZE
    XEWLWEXEWLQJWLQWLVHWLVISVEXRXSEWCWKJZHZEEWCWKVJXRYAEBHZEXTBEXTBAGZWKJBWCYCW
    KABVKVLBAVMSVNWBYBEIZWAWBWPYDWQBEVOVPVQTVRTVSVTTTTVT $.
    $( [9-Oct-2014] $)

  ${
    $d N a $.  $d A a $.  $d B a $.
    $( Membership in a set of lower integers.  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
    ellz1 $p |- ( B e. ZZ -> ( A e. ( ZZ \ ( ZZ>= ` ( B + 1 ) ) ) <-> ( A e. ZZ
        /\ A <_ B ) ) ) $=
      ( cz c1 caddc co cuz cfv cdif wcel wn wa cle wbr eldif clt notbid cr zre
      wb zltp1le lenlt syl2anr peano2z eluz sylan 3bitr4rd pm5.32da syl5bb ) AC
      BDEFZGHZIJACJZAUKJZKZLBCJZULABMNZLACUKOUOULUNUPUOULLZBAPNZKZUJAMNZKUPUNUQ
      URUTBAUAQULARJBRJUPUSTUOASBSABUBUCUQUMUTUOUJCJULUMUTTBUDUJAUEUFQUGUHUI $.
      $( [9-Oct-2014] $)

    $( A set of lower integers and upper integers which abut or overlap is all
       of the integers.  (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
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
       with ` NN ` .  (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
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
    $( Lower integers are countably infinite.  (Contributed by Stefan O'Rear,
       10-Oct-2014.) $)
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
    $( ~ fresaun transposed to mappings.  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
    elmapresaun $p |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\ ( F |` ( A i^i
        B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) e. ( C ^m ( A u. B ) ) )
        $=
      ( cmap co wcel cin cres cun wf cvv wb elmapex1 elmapg sylancl ibi wceq id
      w3a fresaun syl3an unex 3ad2ant1 mpbird ) DCAHIJZECBHIJZDABKZLEUKLUAZUCDE
      MZCABMZHIJZUNCUMNZUIACDNZUJBCENZULULUPUIUQUICOJZAOJUIUQPDCAQZFCADOORSTUJU
      RUJUSBOJUJURPECBQGCBEOORSTULUBABCDEUDUEUIUJUOUPPZULUIUSUNOJVAUTABFGUFCUNU
      MOORSUGUH $.
      $( [9-Oct-2014] $)

    $( ~ fresaunres2 transposed to mappings.  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
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
    $( If two sets are Diophantine, so is their intersection.  (Contributed by
       Stefan O'Rear, 9-Oct-2014.) $)
    diophin $p |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A i^i B )
        e. ( Dioph ` N ) ) $=
      ( vc vg cfv wcel cn0 wa co cres wceq cc0 cz wrex cn a1i syl c2 syl3anc vd
      va ve vb vf cdioph cin wi eldiophelnn0 cv c1 cfz caddc cuz cdif cmap cmzp
      cab cvv cfn wn wss wb id1 zex difexg ax-mp com ominf cen omex nn0z lzenom
      enfi sylancr mtbiri fz1eqin inss1 eqsstrd eldioph2b syl22anc nnenom mp2an
      wbr nnex mtbir elfznn ssriv anbi12d reeanv cexp cmpt inab simplrl simplrr
      cun simprll simprrl eqtr3d eqcomd reseq2d 3eqtr4d elmapresaun nnuz uneq2i
      ad3antrrr syl5eq elmapresaunres2 fveq2d eqtrd simprrr jca32 reseq1 eqeq2d
      eqeq1d syl2anc ex rexlimdvva elmapssres adantr nnssz simprl resabs1 fveq2
      eqtr4d anbi2d cr zssre wf mzpf mp3an23 adantl ffvelrn sseldi mzpresrename
      cle oveq1d 2nn0 mzpexpmpt sylancl 1z nn0p1nn nnge1 lzunuz eleqtrd uneq12d
      oveq2d unidm syl5eqr resundir syl6eqr uncom reseq1i incom simprlr rcla4ev
      simpr difss jca anbi1d rcla42ev rexlimdva impbid mapss sseli sumsqeq0 weq
      nn0ssz oveq12d eqid ovex fvmpt bitr4d rexbidva bitrd syl5bbr abbidv simpl
      fzssuz uzssz sstri pm3.2i simprr mzpaddmpt eldioph2 eqeltrd ineq12 eleq1d
      syl5ibrcom syl5bir sylbid anabsi5 ) ACUFFZGZBUWMGZABUGZUWMGZUWNCHGZUWNUWO
      IZUWQUHACUIUWRUWSADUJZUAUJZUKCULJZKZLZUXAUBUJZFZMLZIZUAHNCUKUMJZUNFZUOZUP
      JZOZDURZLZUBUXKUQFZOZBUWTUCUJZUXBKZLZUXRUDUJZFZMLZIZUCHPUPJZOZDURZLZUDPUQ
      FZOZIZUWQUWRUWNUXQUWOUYJUWRUWRUXKUSGZUXKUTGZVAUXBUXKVBZUWNUXQVCUWRVDZUYLU
      WRNUSGZUYLVENUXJUSVFVGZQUWRUYMVHUTGZVIUWRVHUSGZUXKVHVJWDZUYMUYRVCVKUWRCNG
      ZUYTCVLZCVMRUXKVHUSVNVOVPUWRUXBUXKPUGZUXKCVQZVUCUXKVBUWRUXKPVRQVSZUADAUXK
      CUBVTWAUWRUWRPUSGZPUTGZVAZUXBPVBZUWOUYJVCUYOVUFUWRWEQVUHUWRVUGUYRVIUYSPVH
      VJWDVUGUYRVCVKWBPVHUSVNWCWFQVUIUWRUBUXBPUXECWGWHZQUCDBPCUDVTWAWIUYKUXOUYH
      IZUDUYIOUBUXPOUWRUWQUXOUYHUBUDUXPUYIWJUWRVUKUWQUBUDUXPUYIUWRUXEUXPGZUYAUY
      IGZIZIZUWQVUKUXNUYGUGZUWMGVUOVUPUWTUEUJZUXBKZLZVUQENNUPJZEUJZUXKKZUXEFZSW
      KJZVVAPKZUYAFZSWKJZUMJZWLZFZMLZIZUEHNUPJZOZDURZUWMVUOVUPUXMUYFIZDURVVOUXM
      UYFDWMVUOVVPVVNDVVPUXHUYDIZUCUYEOUAUXLOZVUOVVNUXHUYDUAUCUXLUYEWJVUOVVRVUS
      VUQUXKKZUXEFZMLZVUQPKZUYAFZMLZIZIZUEVVMOZVVNVUOVVRVWGVUOVVQVWGUAUCUXLUYEV
      UOUXAUXLGZUXRUYEGZIZIZVVQVWGVWKVVQIZUXAUXRWPZVVMGUWTVWMUXBKZLZVWMUXKKZUXE
      FZMLZVWMPKZUYAFZMLZIZIZVWGVWLVWMHUXKPWPZUPJZVVMVWLVWHVWIUXAVUCKZUXRVUCKZL
      ZVWMVXEGVUOVWHVWIVVQWNZVUOVWHVWIVVQWOZVWLUXCUXSVXFVXGVWLUWTUXCUXSVWKUXDUX
      GUYDWQZVWKUXHUXTUYCWRZWSUWRVXFUXCLVUNVWJVVQUWRVUCUXBUXAUWRUXBVUCVUDWTZXAX
      FUWRVXGUXSLVUNVWJVVQUWRVUCUXBUXRVXMXAXFXBZUXKPHUXAUXRUYQWEXCTUWRVXEVVMLVU
      NVWJVVQUWRVXDNHUPUWRVXDUXKUKUNFZWPZNPVXOUXKXDXEUWRVUAUKNGZUKUXIYPWDZVXPNL
      VUBVXQUWRUUAQUWRUXIPGVXRCUUBUXIUUCRCUKUUDTXGUUGXFUUEVWLVWOVWRVXAVWLUWTUXC
      UXSWPZVWNVWLUWTUWTUWTWPVXSUWTUUHVWLUWTUXCUWTUXSVXKVXLUUFUUIUXAUXRUXBUUJUU
      KVWLVWQUXFMVWLVWPUXAUXEVWLVWPUXRUXAWPZUXKKZUXAVWMVXTUXKUXAUXRUULUUMVWLVWI
      VWHUXRPUXKUGZKZUXAVYBKZLVYAUXALVXJVXIVWLUXSUXCVYCVYDVWLUWTUXSUXCVXLVXKWSU
      WRVYCUXSLVUNVWJVVQUWRVYBUXBUXRUWRVYBVUCUXBPUXKUUNVXMXGZXAXFUWRVYDUXCLVUNV
      WJVVQUWRVYBUXBUXAVYEXAXFXBPUXKHUXRUXAWEUYQXHTXGXIVWKUXDUXGUYDUUOXJVWLVWTU
      YBMVWLVWSUXRUYAVWLVWHVWIVXHVWSUXRLVXIVXJVXNUXKPHUXAUXRUYQWEXHTXIVWKUXHUXT
      UYCXKXJXLVWFVXCUEVWMVVMVUQVWMLZVUSVWOVWEVXBVYFVURVWNUWTVUQVWMUXBXMXNVYFVW
      AVWRVWDVXAVYFVVTVWQMVYFVVSVWPUXEVUQVWMUXKXMXIXOVYFVWCVWTMVYFVWBVWSUYAVUQV
      WMPXMXIXOWIWIUUPXPXQXRVUOVWFVVRUEVVMVUOVUQVVMGZIZVWFVVRVYHVWFIZVVSUXLGZVW
      BUYEGZUWTVVSUXBKZLZVWAIZUWTVWBUXBKZLZVWDIZIZVVRVYHVYJVWFVYHVYGUXKNVBZUYPV
      YJVUOVYGUUQZVYSVYHNUXJUURZQUYPVYHVEQZVUQHNUXKXSTXTVYHVYKVWFVYHVYGPNVBZUYP
      VYKVYTWUCVYHYAQWUBVUQHNPXSTXTVYIVYNVYPVWDVYIVYMVWAVYIUWTVURVYLVYHVUSVWEYB
      ZVYIUYNVYLVURLUWRUYNVUNVYGVWFVUEXFVUQUXBUXKYCRYEVYHVUSVWAVWDWRUUSVYIUWTVU
      RVYOWUDVYIVUIVYOVURLVUIVYIVUJQVUQUXBPYCRYEVYHVUSVWAVWDXKXLVVQVYRVYNUYDIUA
      UCVVSVWBUXLUYEUXAVVSLZUXHVYNUYDWUEUXDVYMUXGVWAWUEUXCVYLUWTUXAVVSUXBXMXNWU
      EUXFVVTMUXAVVSUXEYDXOWIUUTUXRVWBLZUYDVYQVYNWUFUXTVYPUYCVWDWUFUXSVYOUWTUXR
      VWBUXBXMXNWUFUYBVWCMUXRVWBUYAYDXOWIYFUVATXQUVBUVCVUOVWFVVLUEVVMVYHVWEVVKV
      USVYHVWEVVTSWKJZVWCSWKJZUMJZMLZVVKVYHVVTYGGVWCYGGVWEWUJVCVYHNYGVVTYHVYHNU
      XKUPJZNUXEYIZVVSWUKGZVVTNGVYHVULWULUWRVULVUMVYGWNUXEUXKYJRVYGWUMVUOVYGVUQ
      VUTGZWUMVVMVUTVUQHNVBVVMVUTVBUVHHNNVEVEUVDVGUVEZWUNVYSUYPWUMWUAVEVUQNNUXK
      XSYKRYLWUKNVVSUXEYMXPYNVYHNYGVWCYHVYHNPUPJZNUYAYIZVWBWUPGZVWCNGVYHVUMWUQU
      WRVULVUMVYGWOUYAPYJRVYGWURVUOVYGWUNWURWUOWUNWUCUYPWURYAVEVUQNNPXSYKRYLWUP
      NVWBUYAYMXPYNVVTVWCUVFXPVYHVVJWUIMVYHWUNVVJWUILVYGWUNVUOWUOYLEVUQVVHWUIVU
      TVVIEUEUVGZVVDWUGVVGWUHUMWUSVVCVVTSWKWUSVVBVVSUXEVVAVUQUXKXMXIYQWUSVVFVWC
      SWKWUSVVEVWBUYAVVAVUQPXMXIYQUVIVVIUVJWUGWUHUMUVKUVLRXOUVMYFUVNUVOUVPUVQXG
      VUOUWRUYPUXBNVBZIZVVINUQFZGZVVOUWMGUWRVUNUVRWVAVUOUYPWUTVEUXBVXONUKCUVSUK
      UVTUWAUWBQVUOEVUTVVDWLWVBGZEVUTVVGWLWVBGZWVCVUOEVUTVVCWLWVBGZSHGZWVDVUOUY
      PVYSVULWVFUYPVUOVEQZVYSVUOWUAQUWRVULVUMYBEUXEUXKNYOTYREVVCSNYSYTVUOEVUTVV
      FWLWVBGZWVGWVEVUOUYPWUCVUMWVIWVHWUCVUOYAQUWRVULVUMUWCEUYAPNYOTYREVVFSNYSY
      TEVVDVVGNUWDXPUEDVVINCUWETUWFVUKUWPVUPUWMAUXNBUYGUWGUWHUWIXRUWJUWKRUWL $.
      $( [9-Oct-2014] $)
  $}

  ${
    $d A a b c d e $.  $d B a b c d e $.  $d N a b c d e $.

    $( If two sets are Diophantine, so is their union.  (Contributed by Stefan
       O'Rear, 9-Oct-2014.) $)
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
    $( Diophantine sets are sets of tuples of natural numbers.  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
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
       Diophantine set.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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
       Diophantine.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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
       constrained.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
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

    $( The null set is Diophantine.  (Contributed by Stefan O'Rear,
       10-Oct-2014.) $)
    0dioph $p |- ( A e. NN0 -> (/) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c0 c1 cc0 wceq cfz co cmap crab cdioph cfv wral wne ax-1ne0
      wn df-ne cz mpbi rgenw rabeq0 mpbir cmpt cmzp cvv mzpconstmpt eq0rabdioph
      ovex 1z mp2an mpan2 syl5eqelr ) ACDZEFGHZBCFAIJZKJZLZAMNZUSEHUPRZBUROVABU
      RFGPVAQFGSUAUBUPBURUCUDUOBTUQKJFUEUQUFNDZUSUTDUQUGDFTDVBFAIUJUKBFUQUHULBF
      AUIUMUN $.
      $( [10-Oct-2014] $)

    $( The "universal" set (as large as possible given ~ eldiophss ) is
       Diophantine.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    vdioph $p |- ( A e. NN0 -> ( NN0 ^m ( 1 ... A ) ) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c1 cfz co cmap cc0 wceq crab cdioph wral eqid1 rgenw rabid2
      cfv mpbir cz cmpt cmzp cvv ovex 0z mzpconstmpt mp2an eq0rabdioph syl5eqel
      mpan2 ) ACDZCEAFGZHGZIIJZBULKZALQZULUNJUMBULMUMBULINOUMBULPRUJBSUKHGITUKU
      AQDZUNUODUKUBDISDUPEAFUCUDBIUKUEUFBIAUGUIUH $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for conjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
    anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph /\ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cin inrab diophin syl5eqelr
      ) ACEFDGHIHZJZDKLZMBCSJZUAMNABNCSJTUBOUAABCSPTUBDQR $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for disjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
    orrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph \/ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cun unrab diophun syl5eqelr
      wo ) ACEFDGHIHZJZDKLZMBCTJZUBMNABSCTJUAUCOUBABCTPUAUCDQR $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for conjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
    3anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. (
        NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1
        ... N ) ) | ( ph /\ ps /\ ch ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel w3a wa wb cv df-3an anrabdioph
      a1i rabbiia sylan syl5eqel 3impa ) ADFGEHIJIZKELMZNZBDUFKUGNZCDUFKUGNZABC
      OZDUFKZUGNUHUIPZUJPULABPZCPZDUFKZUGUKUODUFUKUOQDRUFNABCSUAUBUMUNDUFKUGNUJ
      UPUGNABDETUNCDETUCUDUE $.
      $( [10-Oct-2014] $)

    $( Diophantine set builder for disjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
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

  $( A nonempty finite range of integers contains its end point.  (Contributed
     by Stefan O'Rear, 10-Oct-2014.) $)
  elfz1end $p |- ( A e. NN <-> A e. ( 1 ... A ) ) $=
    ( cn wcel c1 cfz co cuz cfv elnnuz biimpi cz nnz uzid eluzfz syl2anc elfznn
    syl impbii ) ABCZADAEFCZSADGHCZAAGHCZTSUAAIJSAKCUBALAMQADANOAAPR $.
    $( [10-Oct-2014] $)

  ${
    $d A c $.  $d B c $.  $d C b $.  $d a c $.  $d b c $.  $d C a $.
    2sbcrex.1 $e |- A e. _V $.
    2sbcrex.2 $e |- B e. _V $.
    $( Exchange an existential quantifier with two substitutions.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
    2sbcrex $p |- ( [ A / a ] [ B / b ] E. c e. C ph <-> E. c e. C [ A / a ] [
        B / b ] ph ) $=
      ( wrex wsbc cvv wcel wb sbcrexg ax-mp sbcbii bitri ) AGDJFCKZEBKZAFCKZGDJ
      ZEBKZUAEBKGDJZBLMZTUCNHSUBEBLCLMSUBNIAFGCDLOPQPUEUCUDNHUAEGBDLOPR $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a b $.  $d a c $.
    $( Exchange a substitution with two existentials.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.) $)
    sbc2rexg $p |- ( A e. V -> ( [ A / a ] E. b e. B E. c e. C ph <-> E. b e. B
        E. c e. C [ A / a ] ph ) ) $=
      ( wcel cvv wrex wsbc wb elex sbcrexg rexbidv bitrd syl ) BEIBJIZAHDKZGCKF
      BLZAFBLHDKZGCKZMBENSUATFBLZGCKUCTFGBCJOSUDUBGCAFHBDJOPQR $.
      $( [11-Oct-2014] $)

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a d $.  $d a e $.
    $( Exchange a substitution with 4 existentials.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.) $)
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
    $( Fully inferenced rewriting under an explicit substitution.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
    sbcbiii $p |- ( [ A / a ] ph <-> [ A / a ] ps ) $=
      ( cvv wcel wsbc wb sbcbii ax-mp ) CGHADCIBDCIJEABDCGFKL $.
      $( [11-Oct-2014] $)
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a c $.  $d a b $.
    $( also my first direct use of ax-4 $)
    $( Rotate a sequence of three explicit substitutions, closed theorem.
       (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
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
       must be manifest sets.  (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    sbcrot3 $p |- ( [ A / a ] [ B / b ] [ C / c ] ph <-> [ B / b ] [ C / c ] [
        A / a ] ph ) $=
      ( cvv wcel wal wsbc wb ax-gen sbcrot3g mp3an ) BKLCKLDKLZFMAGDNFCNEBNAEBN
      GDNFCNOHISFJPABCDKKKEFGQR $.
      $( [11-Oct-2014] $)

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a e $.  $d a d $.
    sbcrot5.4 $e |- D e. _V $.
    sbcrot5.5 $e |- E e. _V $.
    $( Rotate a sequence of five explicit substitutions.  Substituted values
       must be manifest sets.  (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
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
       rewrite the exiting substitution.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
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
    $( Diophantine set builder for existential quantification.  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
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
       substitution.  (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | [ ( t |`
        ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] ph } e. ( Dioph ` M ) ) -> { u e.
        ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cv cfv wsbc co crab wrex wsb ax-17 c1 cfz cres cdioph
      cmap wa hbs1 hbrex weq cbvrexsv sbequ12 rexbidv syl5bb cbvrab wceq cvv wb
      vex dfsbcq sbcbidv mpan2 rexrabdioph syl5eqel ) FKLABEDMZNZOZCVDUAFUBPZUC
      ZOZDKUAEUBPUEPQEUDNLUFABKRZCKVGUEPZQABHSZCISZHKRZIVKQFUDNVJVNCIJVKJMVKLZC
      TVOITVJITVMCHKHMZKLCTVLCIUGUHVJVLHKRCIUIZVNABHKUJVQVLVMHKVLCIUKULUMUNVIVM
      VFCISZHIDEFGVPVEUOZIMZUPLVMVRUQIURVSVLVFCVTUPABVPVEUSUTVAVFCVTVHUSVBVC $.
      $( [11-Oct-2014] $)

    rexfrabdioph.2 $e |- L = ( M + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    2rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... L ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] ph } e. (
        Dioph ` L ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e.
        NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc c1 cfz co wb cvv cv cres cmap crab cdioph wrex vex
      wa resex fvex 2sbcrex a1i rabbiia caddc peano2nn0 syl5eqel adantr sbcrot3
      sbcbiii reseq1 sbccomieg mp2an wss fzssp1 oveq2i syl6sseqr resabs1 dfsbcq
      wceq 3syl wal ax-gen fveq1 sbcco3g cn nn0p1nn elfz1end sylib fvres syl5bb
      sbcbidv mpan2 syl5rbb rabbidv eleq1d biimpa rexfrabdioph syl2anc syldan
      bitrd ) HLMZABFEUAZNZOZCGWLNZOZDWLPHQRZUBZOZELPFQRUCRZUDZFUENZMZABLUFZCGK
      UAZNZODXEWQUBZOZKLPGQRZUCRZUDZGUENZMXDCLUFDLWQUCRUDHUENMWKXCUHZXKACXFODXG
      OZBLUFZKXJUDZXLXHXOKXJXHXOSXEXJMAXGXFLDCBXEWQKUGUIZGXEUJZUKULUMXMGLMZXNBW
      MOZKWLXIUBZOZEWTUDZXBMZXPXLMWKXSXCWKGHPUNRZLIHUOUPUQWKXCYDWKXAYCXBWKWSYBE
      WTYBWNCXFOZDXGOZKYAOZWKWSXTYGYAKWLXIEUGZUIZAWMXGXFBDCFWLUJXQXRURUSYHYFKYA
      OZDYAWQUBZOZWKWSYATMZYLTMYHYMSYJYAWQYJUIYFYAXGYLTTKDXEYAWQUTVAVBWKYMYKDWR
      OZWSWKWQXIVCYLWRVIYMYOSWKWQPYEQRXIPHLVDGYEPQIVEVFWLWQXIVGYKDYLWRVHVJWKWRT
      MYOWSSWLWQYIUIWKYKWPDWRTYKWNCGYANZOZWKWPYNXFTMZKVKYKYQSYJYRKXRVLWNKCYAXFY
      PTTGXEYAVMVNVBWKGXIMZYPWOVIYQWPSWKGVOMYSWKGYEVOIHVPUPGVQVRGXIWLVSWNCYPWOV
      HVJVTWAWBWJVTWCWDWEWFXNBKEFGJWGWHUPXDCDKGHIWGWI $.
      $( [11-Oct-2014] $)

    rexfrabdioph.3 $e |- K = ( L + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables.  (Contributed by Stefan O'Rear,
       17-Oct-2014.) $)
    3rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... K ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] ph } e. ( Dioph ` K ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 ph
        } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc co cvv cv c1 cfz cres cmap crab cdioph wrex wa vex
      wb resex fvex sbc2rexg ax-mp sbcbiii bitri rabbiia caddc nn0p1nn syl5eqel
      a1i cn nnnn0 syl adantr sbcrot3 reseq1 sbccomieg mp2an wceq fzssp1 oveq2i
      wss syl6sseqr resabs1 dfsbcq 3syl wal ax-gen fveq1 sbcco3g elfz1end sylib
      fvres syl5bb sbcbidv syl5bbr rabbidv eleq1d biimpar 2rexfrabdioph syl2anc
      mpan2 bitrd rexfrabdioph syldan ) JOPZABGFUAZQZRCHWSQZRZDIWSQZRZEWSUBJUCS
      ZUDZRZFOUBGUCSUESZUFZGUGQZPZABOUHCOUHZDINUAZQZRZEXMXEUDZRZNOUBIUCSZUESZUF
      ZIUGQZPXLDOUHEOXEUESUFJUGQPWRXKUIZXTADXNRZEXPRZBOUHCOUHZNXSUFZYAXQYENXSXQ
      YEUKXMXSPXQYCBOUHCOUHZEXPRZYEXOYGXPEXMXENUJULZXNTPZXOYGUKIXMUMZAXNOOTDCBU
      NUOUPXPTPYHYEUKYIYCXPOOTECBUNUOUQVBURYBIOPZYDBWTRCXARZNWSXRUDZRZFXHUFZXJP
      ZYFYAPWRYLXKWRIVCPZYLWRIJUBUSSZVCKJUTVAZIVDVEVFWRYQXKWRYPXIXJWRYOXGFXHYOX
      BDXNRZEXPRZNYNRZWRXGUUBYMYNNWSXRFUJZULZUUBYCBWTRCXARZEXPRYMUUAUUFXPEYIAXN
      XAWTDCBYKHWSUMZGWSUMZVGUPYCXPXAWTECBYIUUGUUHVGUQUPUUCUUANYNRZEYNXEUDZRZWR
      XGYNTPZUUJTPUUCUUKUKUUEYNXEUUEULUUAYNXPUUJTTNEXMYNXEVHVIVJWRUUKUUIEXFRZXG
      WRXEXRVNUUJXFVKUUKUUMUKWRXEUBYSUCSXRUBJOVLIYSUBUCKVMVOWSXEXRVPUUIEUUJXFVQ
      VRWRXFTPUUMXGUKWSXEUUDULWRUUIXDEXFTUUIXBDIYNQZRZWRXDUULYJNVSUUIUUOUKUUEYJ
      NYKVTXBNDYNXNUUNTTIXMYNWAWBVJWRIXRPZUUNXCVKUUOXDUKWRYRUUPYTIWCWDIXRWSWEXB
      DUUNXCVQVRWFWGWNWOWFWHWIWJWKYDBCNFGHILMWLWMVAXLDENIJKWPWQ $.
      $( [17-Oct-2014] $)

    rexfrabdioph.4 $e |- J = ( K + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, 4 variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    4rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... J ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] [ ( t ` J ) / y ] ph } e. ( Dioph ` J ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E.
        y e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( cn0 wcel wsbc cvv va cv cfv c1 cfz co cres cmap crab cdioph wrex wa vex
      wb resex fvex 2sbcrex rexbii bitri sbcbiii sbcrexg ax-mp rabbiia cn caddc
      a1i nn0p1nn syl5eqel peano2nn nnnn0 adantr sbcrot3 bitr3i sbccomieg mp2an
      syl reseq1 wss wceq fzssp1 oveq2i syl6sseqr eqeltri eqcomi sseqtri syl6ss
      ovex resabs1 dfsbcq 3syl fveq1 elfz1end sylib sseldi fvres ax-gen sbcco3g
      syl5bb sbcbidv mpan2 rabbidv eleq1d biimpar 2rexfrabdioph syl2anc syldan
      wal bitrd ) LQRZACHGUBZUCZSZBIXJUCZSZDJXJUCZSZEKXJUCZSZFXJUDLUEUFZUGZSZGQ
      UDHUEUFUHUFZUIZHUJUCZRZACQUKZBQUKZDJUAUBZUCZSEKYHUCZSZFYHXSUGZSZUAQUDJUEU
      FZUHUFZUIZJUJUCZRYGDQUKEQUKFQXSUHUFUILUJUCRXIYEULZYPADYISEYJSZFYLSZCQUKZB
      QUKZUAYOUIZYQYMUUBUAYOYMUUBUNYHYORYMYSCQUKZBQUKZFYLSZUUBYKUUEYLFYHXSUAUMU
      OZYKYFDYISEYJSZBQUKUUEYFYJYIQEDBKYHUPZJYHUPZUQUUHUUDBQAYJYIQEDCUUIUUJUQUR
      USUTUUFUUDFYLSZBQUKZUUBYLTRZUUFUULUNUUGUUDFBYLQTVAVBUUKUUABQUUMUUKUUAUNUU
      GYSFCYLQTVAVBURUSUSVFVCYRJQRZYTCXKSBXMSZUAXJYNUGZSZGYBUIZYDRZUUCYQRXIUUNY
      EXIJVDRZUUNXIJKUDVEUFZVDNXIKVDRZUVAVDRXIKLUDVEUFZVDMLVGVHZKVIVPVHZJVJVPVK
      XIUUSYEXIUURYCYDXIUUQYAGYBUUQXNDYISZEYJSZFYLSZUAUUPSZXIYAUUOUVHUUPUAXJYNG
      UMZUOZUUOYSCXKSZBXMSZFYLSUVHYSYLXMXKFBCUUGIXJUPZHXJUPZVLUVMUVGYLFUUGUVMXL
      DYISEYJSZBXMSUVGUVLUVPXMBUVNAXKYJYICEDUVOUUIUUJVLUTXLXMYJYIBEDUVNUUIUUJVL
      USUTVMUTUVIUVGUAUUPSZFUUPXSUGZSZXIYAUUPTRZUVRTRUVIUVSUNUVKUUPXSUVKUOUVGUU
      PYLUVRTTUAFYHUUPXSVQVNVOXIUVSUVQFXTSZYAXIXSYNVRUVRXTVSUVSUWAUNXIXSUDKUEUF
      ZYNXIXSUDUVCUEUFUWBUDLQVTKUVCUDUEMWAWBUWBUDUVAUEUFZYNKTRUWBUWCVRKUVCTMLUD
      VEWGWCUDKTVTVBUVAJUDUEJUVANWDWAWEZWFXJXSYNWHUVQFUVRXTWIWJXIXTTRUWAYAUNXJX
      SUVJUOXIUVQXRFXTTUVQUVFUAUUPSZEKUUPUCZSZXIXRUVTUWFTRUVQUWGUNUVKKUUPUPUVFU
      UPYJUWFTTUAEKYHUUPWKVNVOXIUWGUWEEXQSZXRXIKYNRUWFXQVSUWGUWHUNXIUWBYNKUWDXI
      UVBKUWBRUVDKWLWMWNKYNXJWOUWEEUWFXQWIWJXIXQTRUWHXRUNKXJUPXIUWEXPEXQTUWEXND
      JUUPUCZSZXIXPUVTYITRZUAXGUWEUWJUNUVKUWKUAUUJWPXNUADUUPYIUWITTJYHUUPWKWQVO
      XIJYNRZUWIXOVSUWJXPUNXIUUTUWLUVEJWLWMJYNXJWOXNDUWIXOWIWJWRWSWTXHWRWSWTXHW
      RWRXAXBXCYTCBUAGHIJOPXDXEVHYGDEFUAJKLMNXDXF $.
      $( [11-Oct-2014] $)

    rexfrabdioph.5 $e |- I = ( J + 1 ) $.
    rexfrabdioph.6 $e |- H = ( I + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, 6 variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
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
       substitution, 7 variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    7rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... G ) ) | [ ( t
        |` ( 1 ... N ) ) / u ] [ ( t ` M ) / v ] [ ( t ` L ) / w ] [ ( t ` K )
        / x ] [ ( t ` J ) / y ] [ ( t ` I ) / z ] [ ( t ` H ) / p ] [ ( t ` G )
        / q ] ph } e. ( Dioph ` G ) ) ->
        { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E.
        y e. NN0 E. z e. NN0 E. p e. NN0 E. q e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cv cfv wsbc c1 cfz co cres cmap crab cdioph wa wb vex resex
      wrex cvv sbc2rexg ax-mp sbc4rexg 2rexbii bitri sbcbiii 3bitri a1i rabbiia
      fvex cn caddc nn0p1nn syl5eqel nnnn0 syl adantr sbcrot3 sbcrot5 sbccomieg
      reseq1 mp2an wss wceq fzssp1 oveq2i syl6sseqr resabs1 dfsbcq ax-gen fveq1
      3syl wal sbcco3g elfz1end sylib fvres sbcbidv mpan2 bitrd syl5bbr rabbidv
      syl5bb eleq1d biimpar 6rexfrabdioph syl2anc rexfrabdioph syldan ) PUGUHZA
      QIHUIZUJZUKRJXOUJZUKDKXOUJZUKCLXOUJZUKZBMXOUJZUKENXOUJZUKZFOXOUJZUKZGXOUL
      PUMUNZUOZUKZHUGULIUMUNUPUNZUQZIURUJZUHZAQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZF
      OUFUIZUJZUKZGYOYFUOZUKZUFUGULOUMUNZUPUNZUQZOURUJZUHYNFUGVCGUGYFUPUNUQPURU
      JUHXNYLUSZUUBAFYPUKZGYRUKZQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZUFUUAUQZUUCYSUU
      HUFUUAYSUUHUTYOUUAUHYSUUEQUGVCRUGVCDUGVCCUGVCZBUGVCEUGVCZGYRUKZUUJGYRUKZB
      UGVCEUGVCZUUHYQUUKYRGYOYFUFVAVBZYQYMFYPUKZBUGVCEUGVCZUUKYPVDUHZYQUUQUTOYO
      VNZYMYPUGUGVDFEBVEVFUUPUUJEBUGUGUURUUPUUJUTUUSAYPUGUGUGQUGVDFCDRVGVFVHVIV
      JYRVDUHZUULUUNUTUUOUUJYRUGUGVDGEBVEVFUUMUUGEBUGUGUUTUUMUUGUTUUOUUEYRUGUGU
      GQUGVDGCDRVGVFVHVKVLVMUUDOUGUHZUUFQXPUKRXQUKDXRUKCXSUKZBYAUKZEYBUKZUFXOYT
      UOZUKZHYIUQZYKUHZUUIUUCUHXNUVAYLXNOVOUHZUVAXNOPULVPUNZVOSPVQVRZOVSVTWAXNU
      VHYLXNUVGYJYKXNUVFYHHYIUVFYCFYPUKZGYRUKZUFUVEUKZXNYHUVMUVDUVEUFXOYTHVAZVB
      ZUVMXTFYPUKZBYAUKEYBUKZGYRUKUVQGYRUKZBYAUKZEYBUKUVDUVLUVRYRGUUOXTYPYBYAFE
      BUUSNXOVNZMXOVNZWBVJUVQYRYBYAGEBUUOUWAUWBWBUVTUVCYBEUWAUVSUVBYABUWBUVSUUE
      QXPUKRXQUKDXRUKCXSUKZGYRUKUVBUVQUWCYRGUUOAYPXSXRXQQXPFCDRUUSLXOVNZKXOVNZJ
      XOVNZIXOVNZWCVJUUEYRXSXRXQQXPGCDRUUOUWDUWEUWFUWGWCVIVJVJVKVJUVNUVLUFUVEUK
      ZGUVEYFUOZUKZXNYHUVEVDUHZUWIVDUHUVNUWJUTUVPUVEYFUVPVBUVLUVEYRUWIVDVDUFGYO
      UVEYFWEWDWFXNUWJUWHGYGUKZYHXNYFYTWGUWIYGWHUWJUWLUTXNYFULUVJUMUNYTULPUGWIO
      UVJULUMSWJWKXOYFYTWLUWHGUWIYGWMWPXNYGVDUHUWLYHUTXOYFUVOVBXNUWHYEGYGVDUWHY
      CFOUVEUJZUKZXNYEUWKUURUFWQUWHUWNUTUVPUURUFUUSWNYCUFFUVEYPUWMVDVDOYOUVEWOW
      RWFXNOYTUHZUWMYDWHUWNYEUTXNUVIUWOUVKOWSWTOYTXOXAYCFUWMYDWMWPXGXBXCXDXGXEX
      FXHXIUUFCDRBEUFHIJKLMNOQTUAUBUCUDUEXJXKVRYNFGUFOPSXLXM $.
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
       nonnegative if there is a nonnegative integer equal to it.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
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
       naturals.  (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
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
    $( Diophantine set builder for the less or equals relation.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
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
       integers.  (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    eluzrabdioph $p |- ( ( N e. NN0 /\ M e. ZZ /\ ( t e. ( ZZ ^m ( 1 ... N ) )
        |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) )
        | A e. ( ZZ>= ` M ) } e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv w3a cuz crab cle wbr wral wceq
      cdioph wa wb rabdiophlem1 eluz ralimdv imp sylan2 rabbi sylib 3adant1 cvv
      ex ovex mzpconstmpt mpan lerabdioph syl3an2 eqeltrd ) DEFZCGFZAGHDIJZKJZB
      LVCMNZFZOBCPNFZAEVCKJZQZCBRSZAVHQZDUBNZVBVFVIVKUAZVAVBVFUCVGVJUDZAVHTZVMV
      FVBBGFZAVHTZVOABDUEVBVQVOVBVPVNAVHVBVPVNCBUFUNUGUHUIVGVJAVHUJUKULVBVAAVDC
      LVEFZVFVKVLFVCUMFVBVRHDIUOACVCUPUQACBDURUSUT $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for positivity.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    elnnrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN }
        e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv wa cn crab cuz cdioph wb cv 1z
      elnnuz a1i rabbiia eluzrabdioph mp3an2 syl5eqel ) CDEZAFGCHIZJIBKUILMEZNB
      OEZADUIJIZPBGQMEZAULPZCRMZUKUMAULUKUMSATULEBUBUCUDUHGFEUJUNUOEUAABGCUEUFU
      G $.
      $( [11-Oct-2014] $)

    $( Diophantine set builder for the strict less than relation.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
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
       quantifier-free formulae can be negated.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
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

    $( Divisibility is a Diophantine relation.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
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
       on ` F ` .  Possibly a replacement for ~ fvco2 ?  (Contributed by Stefan
       O'Rear, 16-Oct-2014.) $)
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

    $( A finite set of positive integers is a set of positive integers.
       (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
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
    $( A function with a domain of three elements.  (Contributed by Stefan
       O'Rear, 17-Oct-2014.) $)
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
    $( Membership in ` Dioph ` expressed using a quantified union to add
       witness variables instead of a restriction to remove them.  (Contributed
       by Stefan O'Rear, 16-Oct-2014.) $)
    eldioph4b $p |- ( S e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. p e. ( mzPoly ` (
        W u. ( 1 ... N ) ) ) S = { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0
        ^m W ) ( p ` ( t u. w ) ) = 0 } ) ) $=
      ( vu cfv wcel cn0 cun cc0 wceq wrex cres wa c0 cdioph cv cmap co cfz crab
      c1 cmzp eldiophelnn0 cab cvv cfn wn wb ovex unex jctr intnanr unfir ssun2
      wss pm3.2i eldioph2b sylancl elmapssres mp3an23 adantr ssun1 uncom eqtr4i
      mto resundi wfn nn0ex elmap biimpi ffn fnresdm 3syl syl5eq fveq2d biimpar
      eqeq1d uneq2 rcla4ev syl2anc jca eleq1 rexbidv anbi12d syl5ibrcom expimpd
      wf uneq1 ancomsd rexlimiv cin cn fz1ssnn sslin ax-mp sseqtri reseq2i res0
      ss0 eqtri elmapresaun mp3an3 ancoms reseq1i elmapresaunres2 syl5req simpr
      syl5eqel reseq1 eqeq2d syl12anc rexlimdva imp impbii df-rab eqeq2i rexbii
      fveq2 ex abbii syl6bb biadan2 ) CDUAKLZDMLZCBUBZAUBZNZFUBZKZOPZAMEUCUDZQZ
      BMUGDUEUDZUCUDZUFZPZFEYSNZUHKZQZCDUIYJYICYKJUBZYSRZPZUUFYNKZOPZSZJMUUCUCU
      DZQZBUJZPZFUUDQZUUEYJYJUUCUKLZSUUCULLZUMZYSUUCVAZSYIUUPUNYJUUQEYSGUGDUEUO
      ZUPZUQUUSUUTUUREULLZYSULLZSUVCUVDHUREYSUSVKYSEUTZVBJBCUUCDFVCVDUUOUUBFUUD
      UUNUUACUUNYKYTLZYRSZBUJUUAUUMUVGBUUMUVGUUKUVGJUULUUFUULLZUUJUUHUVGUVHUUJU
      UHUVGUVHUUJSZUVGUUHUUGYTLZUUGYLNZYNKZOPZAYQQZSUVIUVJUVNUVHUVJUUJUVHUUTUUQ
      UVJUVEUVBUUFMUUCYSVEVFVGUVIUUFERZYQLZUUGUVONZYNKZOPZUVNUVHUVPUUJUVHEUUCVA
      UUQUVPEYSVHUVBUUFMUUCEVEVFVGUVHUVSUUJUVHUVRUUIOUVHUVQUUFYNUVHUVQUUFUUCRZU
      UFUVQUVOUUGNUVTUUGUVOVIUUFEYSVLVJUVHUUCMUUFWMZUUFUUCVMUVTUUFPUVHUWAMUUCUU
      FVNUVBVOVPUUCMUUFVQUUCUUFVRVSVTWAWCWBUVMUVSAUVOYQYLUVOPZUVLUVROUWBUVKUVQY
      NYLUVOUUGWDWAWCWEWFWGUUHUVFUVJYRUVNYKUUGYTWHUUHYPUVMAYQUUHYOUVLOUUHYMUVKY
      NYKUUGYLWNWAWCWIWJWKWLWOWPUVFYRUUMUVFYPUUMAYQUVFYLYQLZSZYPUUMUWDYPSYMUULL
      ZYKYMYSRZPZYPUUMUWDUWEYPUWDYMYLYKNZUULYKYLVIZUWCUVFUWHUULLZUWCUVFYLEYSWQZ
      RZYKUWKRZPZUWJUWLTUWMUWLYLTRTUWKTYLUWKTVAUWKTPUWKEWRWQZTYSWRVAUWKUWOVADWS
      YSWREWTXAIXBUWKXEXAZXCYLXDXFUWMYKTRTUWKTYKUWPXCYKXDXFVJZEYSMYLYKGUVAXGXHX
      IXNVGUWDUWGYPUWDUWFUWHYSRZYKYMUWHYSUWIXJUWCUVFUWRYKPZUWCUVFUWNUWSUWQEYSMY
      LYKGUVAXKXHXIXLVGUWDYPXMUUKUWGYPSJYMUULUUFYMPZUUHUWGUUJYPUWTUUGUWFYKUUFYM
      YSXOXPUWTUUIYOOUUFYMYNYDWCWJWEXQYEXRXSXTYFYRBYTYAVJYBYCYGYH $.
      $( [16-Oct-2014] $)

    $( Forward-only version of ~ eldioph4b .  (Contributed by Stefan O'Rear,
       16-Oct-2014.) $)
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
       more variables.  (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
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
    $( Change variable numbers in a Diophantine class abstraction using
       explicit substitution.  (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
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
    $( Change variable numbers in a 3-variable Diophantine class abstraction.
       (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
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

  ${
    $d A x y a b c d $.  $d B x y a b c d $.  $d C y a b c d $.
    $d D x a b c d $.  $d ph x y a b c d $.
    fphpd.a $e |- ( ph -> B ~< A ) $.
    fphpd.b $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    fphpd.c $e |- ( x = y -> C = D ) $.
    $( Pigeonhole principle expressed with implicit substitution.  If the range
       is smaller than the domain, two inputs must be mapped to the same
       output.  (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
    fphpd $p |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ C = D ) ) $=
      ( va vb wceq weq wi wral wn wa wcel ax-17 cv wne wrex cdom wbr csdm nsyl3
      domnsym cvv sdomex simprd syl adantr csb vex wel hbcsb1 hbel eleq1 anbi2d
      hbim csbeq1a eleq1d imbi12d chvar ex wb csbid csbief eqeq12i 2ralbii hbeq
      imbi1i csbeq1 eqeq1d eqeq1 eqeq2d eqeq2 rcla42 sylbir impbid1 syl6 adantl
      com12 id dom2d mpd mtand ancom anbi1i pm4.61 3bitr4i rexbii rexnal sylibr
      df-ne bitri ) AFGMZBCNZOZCDPZBDPZQZBUAZCUAZUBZWRRZCDUCZBDUCZAXBDEUDUEZXJE
      DUFUEZADEUHHUGAXBRZDUISZXJAXMXBAXKXMHXKEUISXMEDUJUKULUMXLKLDEBKUAZFUNZBLU
      AZFUNZUIAXNDSZXOESZOXBAXRXSAXDDSZRZFESZOAXRRZXSOBKYCXSBYCBTBLLXOEBLXNFKUO
      LKUPBTUQZXPESBTURVABKNZYAYCYBXSYEXTXRAXDXNDUSUTYEFXOEBXNFVBVCVDIVEVFUMXBX
      RXPDSRZXOXQMZKLNZVGZOAXBYFYGYHOZYIXBBXDFUNZBXEFUNZMZWSOZCDPBDPZYFYJOYNWTB
      CDDYMWRWSYKFYLGBFVHBKXEFGCUOZXNGSBTJVIVJVMVKYFYOYJYNYJXOYLMZKCNZOBCXNXPDD
      YQYRBBLLXOYLYDBLXEFYPLCUPBTUQVLYRBTVAYJCTYEYMYQWSYRYEYKXOYLBXDXNFVNVOXDXN
      XEVPVDCLNZYQYGYRYHYSYLXQXOBXEXPFVNVQXEXPXNVRVDVSWDVTYJYGYHYJWEBXNXPFVNWAW
      BWCWFWGWHXIXAQZBDUCXCXHYTBDXHWTQZCDUCYTXGUUACDWSQZWRRWRUUBRXGUUAUUBWRWIXF
      UUBWRXDXEWPWJWRWSWKWLWMWTCDWNWQWMXABDWNWQWO $.
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
       reordering.  (Contributed by Stefan O'Rear, 12-Sep-2014.) $)
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
      YEXFWSXAUMVKVLCPVIZYRXTYSYQXGWRWSSVOUUAYEXBXCXGWRXAUMVMVLVPVNVQVSAYIXLWFX
      PXDAYHXKBEAXFETZRZYGXJCEUUCXGETZRZYFXIXHUUEYFXIUUEYDHYEIUUEUUBHFTZYDHQAUU
      BUUDVHUUCUUFUUDADUBZETZRZGFTZWFZUUCUUFWFDBDBVIZUUIUUCUUJUUFUULUUHUUBAUUGX
      FEWGVTUULGHFNWAWBMWCUSDXFGHEFXANXNWDVBUUEUUDIFTZYEIQUUCUUDVGAUUDUUMUUBUUK
      AUUDRZUUMWFDCDCVIZUUIUUNUUJUUMUUOUUHUUDAUUGXGEWGVTUUOGIFOWAWBMWCWEDXGGIEF
      XAOXNWDVBWHWIWJWKWKVEWPWLWMWNWOWQ $.
      $( [12-Sep-2014] $)
  $}

  $( An infinite subset of a countable set is countable, without using choice.
     (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
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
       finitely many buckets.  (Contributed by Stefan O'Rear, 18-Oct-2014.) $)
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
       TODO (Contributed by Stefan O'Rear, 18-Oct-2014.) $)
    fiphp3dOLD $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN ) $=
      ( fiphp3d ) ABCEFGIJKM $.
      $( [18-Oct-2014] $)
  $}

  ${
    $( Value of the numeric cardinality of a nonempty integer range.
       (Contributed by Stefan O'Rear, 12-Sep-2014.) $)
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

    $( Condition for finite ranges to have a strict dominance relation.
       (Contributed by Stefan O'Rear, 12-Sep-2014.) $)
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
       infima; this theorem removes the requirement that A be non-empty.
       (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
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
      $( Value of the canonical numerator function.  (Contributed by Stefan
         O'Rear, 13-Sep-2014.) $)
      qnumval $p |- ( A e. QQ -> ( numer ` A ) = ( 1st ` ( iota_ x e. ( ZZ X.
          NN ) ( ( ( 1st ` x ) gcd ( 2nd ` x ) ) = 1 /\ A = ( ( 1st ` x ) / (
          2nd ` x ) ) ) ) ) ) $=
        ( va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp cq cnumer eqeq1
        crio anbi2d riotabidv fveq2d df-numer fvex fvmpt ) CBADZEFZUGGFZHIJKZCD
        ZUHUILIZKZMZANOPZTZEFUJBULKZMZAUOTZEFQRUKBKZUPUSEUTUNURAUOUTUMUQUJUKBUL
        SUAUBUCACUDUSEUEUF $.
        $( [13-Sep-2014] $)

      $( Value of the canonical denominator function.  (Contributed by Stefan
         O'Rear, 13-Sep-2014.) $)
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

    $( The canonical numerator of a rational is an integer.  (Contributed by
       Stefan O'Rear, 13-Sep-2014.) $)
    qnumcl $p |- ( A e. QQ -> ( numer ` A ) e. ZZ ) $=
      ( cq wcel cnumer cfv cz cdenom cn qnumdencl simpld ) ABCADEFCAGEHCAIJ $.
      $( [13-Sep-2014] $)

    $( The canonical denominator is a positive integer.  (Contributed by Stefan
       O'Rear, 13-Sep-2014.) $)
    qdencl $p |- ( A e. QQ -> ( denom ` A ) e. NN ) $=
      ( cq wcel cnumer cfv cz cdenom cn qnumdencl simprd ) ABCADEFCAGEHCAIJ $.
      $( [13-Sep-2014] $)

    $( Canonical numerator defines a function.  (Contributed by Stefan O'Rear,
       13-Sep-2014.) $)
    fnum $p |- numer : QQ --> ZZ $=
      ( vb va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp crio cq cnumer
      wcel wf wral df-numer fmpt biimpi qnumval qnumcl eqeltrrd mprg ) ACZDEZUI
      FEZGHIJBCZUJUKKHJLAMNOPDEZMSZQMRTZBQUNBQUAUOBQMUMRABUBUCUDULQSULREUMMAULU
      EULUFUGUH $.
      $( [13-Sep-2014] $)

    $( Canonical denominator defines a function.  (Contributed by Stefan
       O'Rear, 13-Sep-2014.) $)
    fden $p |- denom : QQ --> NN $=
      ( vb va cv c1st cfv c2nd cgcd co c1 wceq cdiv wa cz cn cxp crio cq cdenom
      wcel wf wral df-denom fmpt biimpi qdenval qdencl eqeltrrd mprg ) ACZDEZUI
      FEZGHIJBCZUJUKKHJLAMNOPFEZNSZQNRTZBQUNBQUAUOBQNUMRABUBUCUDULQSULREUMNAULU
      EULUFUGUH $.
      $( [13-Sep-2014] $)

    $( Two numbers are the canonical representation of a rational iff they are
       coprime and have the right quotient.  (Contributed by Stefan O'Rear,
       13-Sep-2014.) $)
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

    $( The canonical representation of a rational is fully reduced.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    qnumdencoprm $p |- ( A e. QQ -> ( ( numer ` A ) gcd ( denom ` A ) ) = 1 )
        $=
      ( cq wcel cnumer cfv cdenom cgcd co c1 wceq wa eqidd eqid1 jctir cz cn wb
      cdiv qnumcl qdencl qnumdenbi mpd3an23 mpbird simpld ) ABCZADEZAFEZGHIJZAU
      FUGRHJZUEUHUIKZUFUFJZUGUGJZKZUEUKULUEUFLUGMNUEUFOCUGPCUJUMQASATAUFUGUAUBU
      CUD $.
      $( [13-Sep-2014] $)

    $( Recover a rational number from its canonical representation.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    qeqnumdivden $p |- ( A e. QQ -> A = ( ( numer ` A ) / ( denom ` A ) ) ) $=
      ( cq wcel cnumer cfv cdenom cgcd co c1 wceq wa eqidd eqid1 jctir cz cn wb
      cdiv qnumcl qdencl qnumdenbi mpd3an23 mpbird simprd ) ABCZADEZAFEZGHIJZAU
      FUGRHJZUEUHUIKZUFUFJZUGUGJZKZUEUKULUEUFLUGMNUEUFOCUGPCUJUMQASATAUFUGUAUBU
      CUD $.
      $( [13-Sep-2014] $)

    $( Multiplying a rational by its denominator results in an integer.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    qmuldeneqnum $p |- ( A e. QQ -> ( A x. ( denom ` A ) ) = ( numer ` A ) ) $=
      ( cq wcel cdenom cfv cmul co cnumer cdiv qeqnumdivden oveq1d cc0 wne wceq
      cc cz qnumcl zcn syl cn qdencl nncn nnne0 divcan1 syl3anc eqtrd ) ABCZAAD
      EZFGAHEZUHIGZUHFGZUIUGAUJUHFAJKUGUIOCZUHOCZUHLMZUKUINUGUIPCULAQUIRSUGUHTC
      ZUMAUAZUHUBSUGUOUNUPUHUCSUIUHUDUEUF $.
      $( [13-Sep-2014] $)

    $( A number is an integer iff its negative is.  (Contributed by Stefan
       O'Rear, 13-Sep-2014.) $)
    znegclb $p |- ( A e. CC -> ( A e. ZZ <-> -u A e. ZZ ) ) $=
      ( cc wcel cz cneg znegcl negneg eleq1d syl5ib impbid2 ) ABCZADCZAEZDCZAFN
      MEZDCKLMFKOADAGHIJ $.
      $( [13-Sep-2014] $)

    $( A number which is less than zero is not zero.  (Contributed by Stefan
       O'Rear, 13-Sep-2014.) $)
    lt0ne0 $p |- ( ( A e. RR /\ A < 0 ) -> A =/= 0 ) $=
      ( cr wcel cc0 clt wbr wa wne 0re ltne mp3an2 necomd ) ABCZADEFZGDAMDBCNDA
      HIADJKL $.
      $( [13-Sep-2014] $)

    $( Strong form of ~ divides2 for natural numbers.  (Contributed by Stefan
       O'Rear, 13-Sep-2014.) $)
    nndivdivides $p |- ( ( A e. NN /\ B e. NN ) -> ( B || A <-> ( A / B ) e. NN
        ) ) $=
      ( cn wcel wa cdivides wbr cc0 cdiv co clt cz wne wb adantl adantr cr nnre
      nnz nngt0 nnne0 divides2 syl3anc anbi1d divgt0 syl22anc elnnz a1i 3bitr4d
      biantrud ) ACDZBCDZEZBAFGZHABIJZKGZEUOLDZUPEZUNUOCDZUMUNUQUPUMBLDZBHMZALD
      ZUNUQNULUTUKBSOULVAUKBUAOUKVBULASPBAUBUCUDUMUPUNUMAQDZHAKGZBQDZHBKGZUPUKV
      CULARPUKVDULATPULVEUKBROULVFUKBTOABUEUFUJUSURNUMUOUGUHUI $.
      $( [13-Sep-2014] $)

    $( Calculate the reduced form of a quotient using ` gcd ` .  (Contributed
       by Stefan O'Rear, 13-Sep-2014.) $)
    divnumden $p |- ( ( A e. ZZ /\ B e. NN ) -> ( ( numer ` ( A / B ) ) = ( A /
        ( A gcd B ) ) /\ ( denom ` ( A / B ) ) = ( B / ( A gcd B ) ) ) ) $=
      ( cz wcel cn wa cgcd co cdiv c1 cfv wb cdivides wbr sylan2 cc0 syl adantl
      wceq cc cnumer cdenom cq znq nnz gcddvds simpld wne cn0 gcdcl simpl nnne0
      nn0z wn df-ne sylib intnand gcdn0cl syl21anc divides2 syl3anc mpbid simpr
      simprd nndivdivides syl2anc qnumdenbi gcddiv syl31anc divid eqtr3d adantr
      nncn zcn w3a divcan7 eqcomd syl122anc mpbi2and ) ACDZBEDZFZAABGHZIHZBWCIH
      ZGHZJSZABIHZWDWEIHZSZWHUAKWDSWHUBKWESFZWBWHUCDWDCDZWEEDZWGWJFWKLABUDWBWCA
      MNZWLWBWNWCBMNZWAVTBCDZWNWOFZBUEZABUFOZUGWBWCCDZWCPUHZVTWNWLLWAVTWPWTWRVT
      WPFWCUIDWTABUJWCUMQOWBWCEDZXAWBVTWPAPSZBPSZFUNXBVTWAUKZWAWPVTWRRZWBXDXCWA
      XDUNZVTWABPUHZXGBULZBPUOUPRUQABURUSZWCULQZXEWCAUTVAVBWBWOWMWBWNWOWSVDWBWA
      XBWOWMLVTWAVCXJBWCVEVFVBWHWDWEVGVAWBWCWCIHZWFJWBVTWPXBWQXLWFSXEXFXJWSABWC
      VHVIWBWCTDZXAXLJSWBXBXMXJWCVMQZXKWCVJVFVKWBATDZBTDZXHXMXAWJVTXOWAAVNVLWAX
      PVTBVMRWAXHVTXIRXNXKXOXPXHFXMXAFVOWIWHABWCVPVQVRVS $.
      $( [13-Sep-2014] $)

    $( Reducing a quotient never increases the denominator.  (Contributed by
       Stefan O'Rear, 13-Sep-2014.) $)
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

    $( A rational is positive iff its canonical numerator is.  (Contributed by
       Stefan O'Rear, 15-Sep-2014.) $)
    qnumgt0 $p |- ( A e. QQ -> ( 0 < A <-> 0 < ( numer ` A ) ) ) $=
      ( cq wcel cc0 clt wbr cdenom cfv cmul co cnumer cr wb 0re a1i qre cn nnre
      qdencl syl nngt0 ltmul1 syl112anc cc wceq nncn mul02 qmuldeneqnum breq12d
      3syl bitrd ) ABCZDAEFZDAGHZIJZAUNIJZEFZDAKHZEFULDLCZALCUNLCZDUNEFZUMUQMUS
      ULNOAPULUNQCZUTASZUNRTULVBVAVCUNUATDAUNUBUCULUODUPUREULVBUNUDCUODUEVCUNUF
      UNUGUJAUHUIUK $.
      $( [15-Sep-2014] $)

    $( A rational is positive iff its canonical numerator is a natural number.
       (Contributed by Stefan O'Rear, 15-Sep-2014.) $)
    qgt0numnn $p |- ( ( A e. QQ /\ 0 < A ) -> ( numer ` A ) e. NN ) $=
      ( cq wcel cc0 clt wbr wa cnumer cfv cz qnumcl adantr qnumgt0 biimpa elnnz
      cn sylanbrc ) ABCZDAEFZGAHIZJCZDTEFZTPCRUASAKLRSUBAMNTOQ $.
      $( [15-Sep-2014] $)

    $( The square of a rational is rational.  (Contributed by Stefan O'Rear,
       15-Sep-2014.) $)
    qsqcl $p |- ( A e. QQ -> ( A ^ 2 ) e. QQ ) $=
      ( cq wcel c2 cexp co cmul cc wceq qcn sqval syl qmulcl anidms eqeltrd ) A
      BCZADEFZAAGFZBPAHCQRIAJAKLPRBCAAMNO $.
      $( [15-Sep-2014] $)

    $( Squaring commutes with GCD, in particular two coprime numbers have
       coprime squares.  (Contributed by Stefan O'Rear, 15-Sep-2014.) $)
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

    $( ~ nn0gcdsq extended to integers by symmetry.  (Contributed by Stefan
       O'Rear, 15-Sep-2014.) $)
    zgcdsq $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A gcd B ) ^ 2 ) = ( ( A ^ 2 )
        gcd ( B ^ 2 ) ) ) $=
      ( cz wcel wa cgcd co c2 cexp cabs cfv gcdabs eqcomd cn0 wceq nn0abscl zre
      cr absresq syl oveq1d nn0gcdsq syl2an adantr adantl oveq12d 3eqtrd ) ACDZ
      BCDZEZABFGZHIGAJKZBJKZFGZHIGZULHIGZUMHIGZFGZAHIGZBHIGZFGUJUKUNHIUJUNUKABL
      MUAUHULNDUMNDUOUROUIAPBPULUMUBUCUJUPUSUQUTFUJARDZUPUSOUHVAUIAQUDASTUJBRDZ
      UQUTOUIVBUHBQUEBSTUFUG $.
      $( [15-Sep-2014] $)

    $( Squaring a rational squares its canonical components.  (Contributed by
       Stefan O'Rear, 15-Sep-2014.) $)
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

    $( Square commutes with canonical numerator.  (Contributed by Stefan
       O'Rear, 15-Sep-2014.) $)
    numsq $p |- ( A e. QQ -> ( numer ` ( A ^ 2 ) ) = ( ( numer ` A ) ^ 2 ) ) $=
      ( cq wcel c2 cexp co cnumer cfv wceq cdenom numdensq simpld ) ABCADEFZGHA
      GHDEFIMJHAJHDEFIAKL $.
      $( [15-Sep-2014] $)

    $( Square commutes with canonical denominator.  (Contributed by Stefan
       O'Rear, 15-Sep-2014.) $)
    densq $p |- ( A e. QQ -> ( denom ` ( A ^ 2 ) ) = ( ( denom ` A ) ^ 2 ) ) $=
      ( cq wcel c2 cexp co cnumer cfv wceq cdenom numdensq simprd ) ABCADEFZGHA
      GHDEFIMJHAJHDEFIAKL $.
      $( [15-Sep-2014] $)

    $( A rational is an integer iff it has denominator 1.  (Contributed by
       Stefan O'Rear, 15-Sep-2014.) $)
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
       integer.  (Contributed by Stefan O'Rear, 15-Sep-2014.) $)
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
       square root.  (Contributed by Stefan O'Rear, 15-Sep-2014.) $)
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
       than the difference between the endpoints.  (Contributed by Stefan
       O'Rear, 12-Sep-2014.) $)
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

    $( Modular reduction produces a half-open interval.  (Contributed by Stefan
       O'Rear, 12-Sep-2014.) $)
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
      1z zre ad2antll posdif biimpa eqbrtrd zlem1lt mpbird 3syl resubcl elfzle1
      0re nnre lesub2 mpbid subid1 elfzle2 letrd mpbir2and adantrr rpre remulcl
      ad3antrrr flcl simpr ltle syl21anc rpgt0 lemul2 syl112anc flwordi biimpar
      subge0 elnn0z sylanbrc oveq1d sub4 syl22anc modfrac eqcomd oveq12d 3eqtrd
      imp subdi fveq2d modcl abssub eqtr2d breq1d biimpd impr oveq2 rcla42ev ex
      1rp rexlimdvva mpd ) CUCEZDUDEZFZUAUEZUBUEZGHZCYIUFIZJUGIZCYJUFIZJUGIZKIL
      UHZJDUIIZGHZFZUBMDUJIZUKUAYTUKCAUEZUFIZBUEZKIZLUHZYQGHZBULUKAJDUJIZUKZUAU
      BCDUMYHYSUUHUAUBYTYTYHYIYTEZYJYTEZFZFZYSUUHUULYSFYJYIKIZUUGEZYNUQUHZYLUQU
      HZKIZULEZCUUMUFIZUUQKIZLUHZYQGHZUUHUULYKUUNYRUULYKFZUUNJUUMNHZUUMDNHZUVCU
      UMUNEZJUNEZDUNEZUUNUVDUVEFURUVCYJUNEZYIUNEZUVFUVCUUJUVIYHUUIUUJYKUOZYJMDU
      PZOUVCUUIUVJYHUUIUUJYKUSZYIMDUPZOYJYIUTPZUVGUVCVIVAZUVCYGUVHYFYGUUKYKVBZD
      VCOUUMJDVDVEUVCUVDJJKIZUUMGHZUVCUVRMUUMGUVRMQUVCJVFVGVAUULYKMUUMGHZUULYIR
      EZYJREZYKUVTURUULUVJUWAUUIUVJYHUUJUVNVHYIVJZOUULUVIUWBUUJUVIYHUUIUVLVKYJV
      JZOYIYJVLPVMVNUVCUVGUVFUVDUVSURUVPUVOJUUMVOPVPUVCUUMYJMKIZDUVCUWBUWAUUMRE
      UVCUUJUVIUWBUVKUVLUWDVQZUVCUUIUVJUWAUVMUVNUWCVQZYJYIVRPUVCUWBMREZUWEREUWF
      UWHUVCVTVAZYJMVRPUVCYGDREUVQDWAOUVCMYINHZUUMUWENHZUVCUUIUWJUVMYIMDVSOUVCU
      WHUWAUWBUWJUWKURUWIUWGUWFMYIYJWBVEWCUVCUWEYJDNUVCYJSEZUWEYJQUVCYJUWFTZYJW
      DOUVCUUJYJDNHUVKYJMDWEOVNWFWGWHUULYKUURYRUVCUUQUNEZMUUQNHZUURUVCUUOUNEZUU
      PUNEZUWNUVCYNREZUWPUVCCREZUWBUWRYFUWSYGUUKYKCWIWKZUWFCYJWJPZYNWLOZUVCYLRE
      ZUWQUVCUWSUWAUXCUWTUWGCYIWJPZYLWLOZUUOUUPUTPUVCUUOREZUUPREZUUPUUONHZUWOUV
      CUWPUXFUXBUUOVJOZUVCUWQUXGUXEUUPVJOZUVCUXCUWRYLYNNHZUXHUXDUXAUVCYIYJNHZUX
      KUVCUWAUWBYKUXLUWGUWFUULYKWMUWAUWBFYKUXLYIYJWNXKWOUVCUWAUWBUWSMCGHZUXLUXK
      URUWGUWFUWTYFUXMYGUUKYKCWPWKYIYJCWQWRWCYLYNWSVEUXFUXGFUWOUXHUUOUUPXAWTWOU
      UQXBXCWHUULYKYRUVBUVCYRUVBUVCYPUVAYQGUVCUVAYOYMKIZLUHZYPUVCUUTUXNLUVCUUTY
      NYLKIZUUQKIZYNUUOKIZYLUUPKIZKIZUXNUVCUUSUXPUUQKUVCCSEUWLYISEUUSUXPQUVCCUW
      TTUWMUVCYIUWGTCYJYIXLVEXDUVCYNSEYLSEUUOSEUUPSEUXQUXTQUVCYNUXATUVCYLUXDTUV
      CUUOUXITUVCUUPUXJTYNYLUUOUUPXEXFUVCUXRYOUXSYMKUVCYOUXRUVCUWRYOUXRQUXAYNXG
      OXHUVCYMUXSUVCUXCYMUXSQUXDYLXGOXHXIXJXMUVCYOSEYMSEUXOYPQUVCYOUVCUWRJUCEZY
      OREUXAUYAUVCYCVAZYNJXNPTUVCYMUVCUXCUYAYMREUXDUYBYLJXNPTYOYMXOPXPXQXRXSUUF
      UVBUUSUUCKIZLUHZYQGHABUUMUUQUUGULUUAUUMQZUUEUYDYQGUYEUUDUYCLUYEUUBUUSUUCK
      UUAUUMCUFXTXDXMXQUUCUUQQZUYDUVAYQGUYFUYCUUTLUUCUUQUUSKXTXMXQYAVEYBYDYE $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Eliminate ranges, use positivity of the input to
       force positivity of the output by increasing ` B ` as needed. $)
    irrapxlem4 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. NN E. y e. NN ( abs `
        ( ( A x. x ) - y ) ) < ( 1 / if ( x <_ B , B , x ) ) ) $=
      ( va wcel cn wa co cmin c1 cdiv cle wbr clt cr cc0 syl2anc syl wb vb cmul
      crp cv cabs cfv cfl caddc cif cn0 wrex cfz simpl rpreccl rprege0 flge0nn0
      3syl nn0p1nn simpr ifcl irrapxlem3 simpllr elfznn nn0z ad2antlr ad3antrrr
      cz cneg cc rpre nnre remulcl nn0re resubcl recnd abscl wne rereccl 0reALT
      nnne0 a1i rpne0 flcl zre peano2re max2 nngt0 ltletrd lerec syl22anc mpbid
      max1 flltp1 ltle mpd wceq nncn recrec breqtrrd recgt0 rpgt0 mpbird mulid1
      wi letrd nnge1 1re lemul2 syl112anc eqbrtrrd subid1 simprd ltsub2 syl3anc
      abslt elnnz sylanbrc redivcl elfzle2 jca maxle weq oveq2 oveq1d fveq2d id
      breq1 ifbieq2d oveq2d breq12d breq1d rcla42ev ex rexlimdva ) CUCFZDGFZHZC
      EUDZUBIZUAUDZJIZUEUFZKDKCLIZUGUFZKUHIZMNZUUEDUIZLIZONZUAUJUKZEKUUGULIZUKZ
      CAUDZUBIZBUDZJIZUEUFZKUUMDMNZDUUMUIZLIZONZBGUKAGUKZYQYOUUGGFZUULYOYPUMZYQ
      UUEGFZYPUVCYQUUCPFZQUUCMNHZUUDUJFUVEYQYOUUCUCFUVGUVDCUNUUCUOUQUUCUPUUDURU
      QZYOYPUSZUUFUUEDGUTZREUACUUGVARYQUUJUVBEUUKYQYRUUKFZHZUUIUVBUAUJUVLYTUJFZ
      HZUUIUVBUVNUUIHZYRGFZYTGFZUUBKYRDMNZDYRUIZLIZONZUVBUVOUVKUVPYQUVKUVMUUIVB
      ZYRUUGVCSZUVOYTVGFZQYTONZUVQUVMUWDUVLUUIYTVDVEUVOUWEUUAYSQJIZONZUVOUWFVHU
      UAONZUWGUVOUUBUWFONZUWHUWGHZUVOUUBUUHUWFUVOUUAVIFUUBPFUVOUUAUVOYSPFZYTPFZ
      UUAPFZUVOCPFZYRPFZUWKUVOYOUWNYQYOUVKUVMUUIUVDVFZCVJSZUVOUVPUWOUWCYRVKSZCY
      RVLRZUVMUWLUVLUUIYTVMVEZYSYTVNRZVOUUAVPSZUVOUUGPFZUUGQVQZUUHPFUVOUVCUXCUV
      OUVEYPUVCYQUVEUVKUVMUUIUVHVFZYQYPUVKUVMUUIUVIVFZUVJRZUUGVKSZUVOUVCUXDUXGU
      UGVTSUUGVRRZUVOUWKQPFZUWFPFZUWSUXJUVOVSWAZYSQVNRZUVNUUIUSZUVOUUHCUWFUXIUW
      QUXMUVOUUHKUUELIZCUXIUVOUUEPFZUUEQVQZUXOPFZUVOUUDPFZUXPUVOUVFUUDVGFUXSUVO
      UWNCQVQZUVFUWQUVOYOUXTUWPCWBSCVRRZUUCWCUUDWDUQUUDWESZUVOUVEUXQUXEUUEVTSZU
      UEVRRZUWQUVOUUEUUGMNZUUHUXOMNZUVODPFZUXPUYEUVOYPUYGUXFDVKSZUYBDUUEWFRUVOU
      XPQUUEONZUXCQUUGONZUYEUYFTUYBUVOUVEUYIUXEUUEWGSZUXHUVOQDUUGUXLUYHUXHUVOYP
      QDONUXFDWGSZUVOUYGUXPDUUGMNZUYHUYBDUUEWLRZWHZUUEUUGWIWJWKUVOUXOCMNZUUCKUX
      OLIZMNZUVOUUCUUEUYQMUVOUUCUUEONZUUCUUEMNZUVOUVFUYSUYAUUCWMSUVOUVFUXPUYSUY
      TXDUYAUYBUUCUUEWNRWOUVOUUEVIFZUXQUYQUUEWPUVOUVEVUAUXEUUEWQSUYCUUEWRRWSUVO
      UXRQUXOONZUWNQCONZUYPUYRTUYDUVOUXPUYIVUBUYBUYKUUEWTRUWQUVOYOVUCUWPCXASZUX
      OCWIWJXBXEUVOCYSUWFMUVOCKUBIZCYSMUVOCVIFVUECWPUVOCUWQVOCXCSUVOKYRMNZVUEYS
      MNZUVOUVPVUFUWCYRXFSUVOKPFZUWOUWNVUCVUFVUGTVUHUVOXGWAZUWRUWQVUDKYRCXHXIWK
      XJUVOYSVIFUWFYSWPUVOYSUWSVOYSXKSWSXEWHUVOUWMUXKUWIUWJTUXAUXMUUAUWFXORWKXL
      UVOUXJUWLUWKUWEUWGTUXLUWTUWSQYTYSXMXNXBYTXPXQUVOUUBUUHUVTUXBUXIUVOVUHUVSP
      FZUVSQVQZUVTPFVUIUVOUVSGFZVUJUVOYPUVPVULUXFUWCUVRDYRGUTRZUVSVKSUVOVULVUKV
      UMUVSVTSKUVSXRXNUXNUVOUVSUUGMNZUUHUVTMNZUVOVUNYRUUGMNZUYMHZUVOVUPUYMUVOUV
      KVUPUWBYRKUUGXSSUYNXTUVOUWOUYGUXCVUNVUQTUWRUYHUXHYRDUUGYAXNXBUVOVUJQUVSON
      UXCUYJVUNVUOTUVOUYGUWOVUJUYHUWRUVRDYRPUTRZUVOQDUVSUXLUYHVURUYLUVOUWOUYGDU
      VSMNUWRUYHYRDWFRWHUXHUYOUVSUUGWIWJWKWHUVAUWAYSUUOJIZUEUFZUVTONABYRYTGGAEY
      BZUUQVUTUUTUVTOVVAUUPVUSUEVVAUUNYSUUOJUUMYRCUBYCYDYEVVAUUSUVSKLVVAUURUVRU
      UMYRDUUMYRDMYGVVAYFYHYIYJBUAYBZVUTUUBUVTOVVBVUSUUAUEUUOYTYSJYCYEYKYLXNYMY
      NYNWO $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Switching to real intervals and fraction
       syntax. $)
    irrapxlem5 $p |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. QQ ( 0 < x /\ ( abs
        ` ( x - A ) ) < B /\ ( abs ` ( x - A ) ) < ( ( denom ` x ) ^ -u 2 ) ) )
        $=
      ( crp wcel cmul co cabs cfv c1 cdiv cle wbr clt cc0 cr syl syl2anc wceq
      cc va vb wa cv cmin cfl caddc cif cn wrex cdenom c2 cneg w3a cq cn0 simpr
      cexp rpreccl rpre jca flge0nn0 nn0p1nn 3syl irrapxlem4 syldan wne simplrr
      rpge0 nnq simplrl nnne0 qdivcl syl3anc nnrp rpgt0 nnre nnnn0 nn0ge0 absid
      rpdivcl eqcomd oveq1d recnd qre ad3antrrr resubcl absmul qcn rpcn divcan2
      subdi mulcom oveq12d eqtrd fveq2d remulcl 3eqtr2d recn abscl simpllr ifcl
      abssub gt0ne0 rereccl flltp1 ltle imp syl21anc letrd lerec syl22anc mpbid
      max2 wb rpne0 recrec mulid2 eqtr4d nnge1 1re a1i lemul1 syl112anc eqbrtrd
      ltletrd nngt0 ltmul2 mpbird msqgt0 qdencl max1 divdiv1 syl122anc 3eqtr3rd
      divid divrec 3brtr4d cz nnz divdenle le2msq nncn 2nn0 expneg sqval oveq2d
      breqtrrd breq2 oveq1 breq1d breq12d 3anbi123d rcla4ev syl13anc rexlimdvva
      fveq2 ex mpd ) BDEZCDEZUCZBUAUDZFGZUBUDZUEGZHIZJUVCJCKGZUFIZJUGGZLMZUVJUV
      CUHZKGZNMZUBUIUJUAUIUJZOAUDZNMZUVPBUEGZHIZCNMZUVSUVPUKIZULUMZURGZNMZUNZAU
      OUJZUUTUVAUVJUIEZUVOUVBUVHPEZOUVHLMZUCUVIUPEZUWGUVBUWHUWIUVBUVHDEZUWHUVBU
      VAUWKUUTUVAUQCUSZQZUVHUTZQUVBUWKUWIUWMUVHVIZQVAUVHVBZUVIVCZVDUAUBBUVJVEVF
      UVBUVNUWFUAUBUIUIUVBUVCUIEZUVEUIEZUCZUCZUVNUWFUXAUVNUCZUVEUVCKGZUOEZOUXCN
      MZUXCBUEGZHIZCNMZUXGUXCUKIZUWBURGZNMZUWFUXBUVEUOEZUVCUOEZUVCOVGZUXDUXBUWS
      UXLUVBUWRUWSUVNVHZUVEVJQUXBUWRUXMUVBUWRUWSUVNVKZUVCVJQUXBUWRUXNUXPUVCVLQZ
      UVEUVCVMVNZUXBUXCDEZUXEUXBUVEDEZUVCDEZUXSUXBUWSUXTUXOUVEVOQUXBUWRUYAUXPUV
      CVOQZUVEUVCWARUXCVPQUXBUXHUVCUXGFGZUVCCFGZNMZUXBUYCUVGUYDNUXBUYCUVCHIZUXG
      FGZUVCUXFFGZHIZUVGUXBUVCUYFUXGFUXBUYFUVCUXBUVCPEZOUVCLMZUYFUVCSUXBUWRUYJU
      XPUVCVQQZUXBUWRUVCUPEUYKUXPUVCVRUVCVSVDZUVCVTRWBWCUXBUVCTEZUXFTEZUYIUYGSU
      XBUVCUYLWDZUXBUXFUXBUXCPEZBPEZUXFPEZUXBUXDUYQUXRUXCWEQUUTUYRUVAUWTUVNBUTW
      FZUXCBWGRZWDUVCUXFWHRUXBUYIUVEUVDUEGZHIZUVGUXBUYHVUBHUXBUYHUVCUXCFGZUVCBF
      GZUEGZVUBUXBUYNUXCTEZBTEZUYHVUFSUYPUXBUXDVUGUXRUXCWIQUUTVUHUVAUWTUVNBWJWF
      ZUVCUXCBWLVNUXBVUDUVEVUEUVDUEUXBUVETEZUYNUXNVUDUVESUXBUVEUXBUWSUVEPEZUXOU
      VEVQQZWDZUYPUXQUVEUVCWKVNUXBUYNVUHVUEUVDSUYPVUIUVCBWMRWNWOWPUXBVUJUVDTEVU
      CUVGSVUMUXBUVDUXBUYRUYJUVDPEZUYTUYLBUVCWQRZWDUVEUVDXCRWOWRZUXBUVGUVMUYDUX
      BUVFPEZUVFTEUVGPEUXBVUNVUKVUQVUOVULUVDUVEWGRUVFWSUVFWTVDZUXBUVLPEZUVLOVGZ
      UVMPEUXBUVJPEZUYJVUSUXBUWGVVAUXBUWJUWGUXBUWHUWIUWJUXBUWKUWHUXBUVAUWKUUTUV
      AUWTUVNXAZUWLQZUWNQZUXBUWKUWIVVCUWOQUWPRUWQQZUVJVQQZUYLUVKUVJUVCPXBRZUXBV
      USOUVLNMZVUTVVGUXBUVLDEZVVHUXBUVJDEZUYAVVIUXBUWGVVJVVEUVJVOQUYBUVKUVJUVCD
      XBRUVLVPQZUVLXDRUVLXERZUXBUYJCPEZUYDPEUYLUXBUVAVVMVVBCUTQZUVCCWQRZUXAUVNU
      QZUXBUVMJUVHKGZUYDVVLUXBUWKVVQDEVVQPEVVCUVHUSVVQUTVDVVOUXBUVHUVLLMZUVMVVQ
      LMZUXBUVHUVJUVLVVDVVFVVGUXBUWHVVAUVHUVJNMZUVHUVJLMZVVDVVFUXBUWHVVTVVDUVHX
      FQUWHVVAUCVVTVWAUVHUVJXGXHXIUXBUYJVVAUVJUVLLMUYLVVFUVCUVJXNRXJUXBUWHOUVHN
      MZVUSVVHVVRVVSXOVVDUXBUWKVWBVVCUVHVPQVVGVVKUVHUVLXKXLXMUXBVVQJCFGZUYDLUXB
      VVQCVWCUXBCTEZCOVGZVVQCSUXBCVVNWDZUXBUVAVWEVVBCXPQCXQRUXBVWDVWCCSVWFCXRQX
      SUXBJUVCLMZVWCUYDLMZUXBUWRVWGUXPUVCXTQUXBJPEZUYJVVMOCNMZVWGVWHXOVWIUXBYAY
      BUYLVVNUXBUVAVWJVVBCVPQJUVCCYCYDXMYEXJYFYEUXBUXGPEZVVMUYJOUVCNMZUXHUYEXOU
      XBUYSUYOVWKVUAUXFWSUXFWTVDZVVNUYLUXBUWRVWLUXPUVCYGQZUXGCUVCYHYDYIUXBUXGJU
      XIUXIFGZKGZUXJNUXBUXGJUVCUVCFGZKGZVWPVWMUXBVWQPEZVWQOVGZVWRPEZUXBUYJUYJVW
      SUYLUYLUVCUVCWQRZUXBVWSOVWQNMZVWTVXBUXBUYJUXNVXCUYLUXQUVCYJRZVWQXDRZVWQXE
      RZUXBVWOPEZVWOOVGZVWPPEUXBUXIPEZVXIVXGUXBUXIUIEZVXIUXBUXDVXJUXRUXCYKQZUXI
      VQQZVXLUXIUXIWQRZUXBVXGOVWONMZVXHVXMUXBVXIUXIOVGZVXNVXLUXBVXJVXOVXKUXIVLQ
      UXIYJRZVWOXDRVWOXERUXBUXGVWRNMZUYCUVCVWRFGZNMZUXBUVGJUVCKGZUYCVXRNUXBUVGU
      VMVXTVURVVLUXBUYJUXNVXTPEUYLUXQUVCXERVVPUXBUVCUVLLMZUVMVXTLMZUXBUYJVVAVYA
      UYLVVFUVCUVJYLRUXBUYJVWLVUSVVHVYAVYBXOUYLVWNVVGVVKUVCUVLXKXLXMYFVUPUXBUVC
      UVCKGZUVCKGZUVCVWQKGZVXTVXRUXBUYNUYNUXNUYNUXNVYDVYESUYPUYPUXQUYPUXQUVCUVC
      UVCYMYNUXBVYCJUVCKUXBUYNUXNVYCJSUYPUXQUVCYPRWCUXBUYNVWQTEVWTVYEVXRSUYPUXB
      VWQVXBWDVXEUVCVWQYQVNYOYRUXBVWKVXAUYJVWLVXQVXSXOVWMVXFUYLVWNUXGVWRUVCYHYD
      YIUXBVWOVWQLMZVWRVWPLMZUXBUXIUVCLMZVYFUXBUVEYSEZUWRVYHUXBUWSVYIUXOUVEYTQU
      XPUVEUVCUUARUXBVXIOUXILMZUYJUYKVYHVYFXOVXLUXBVXJUXIUPEVYJVXKUXIVRUXIVSVDU
      YLUYMUXIUVCUUBXLXMUXBVXGVXNVWSVXCVYFVYGXOVXMVXPVXBVXDVWOVWQXKXLXMYFUXBUXJ
      JUXIULURGZKGZVWPUXBUXITEZULUPEZUXJVYLSUXBVXJVYMVXKUXIUUCQZVYNUXBUUDYBUXIU
      LUUERUXBVYKVWOJKUXBVYMVYKVWOSVYOUXIUUFQUUGWOUUHUWEUXEUXHUXKUNAUXCUOUVPUXC
      SZUVQUXEUVTUXHUWDUXKUVPUXCONUUIVYPUVSUXGCNVYPUVRUXFHUVPUXCBUEUUJWPZUUKVYP
      UVSUXGUWCUXJNVYQVYPUWAUXIUWBURUVPUXCUKUUQWCUULUUMUUNUUOUURUUPUUS $.
      $( [13-Sep-2014] $)

    $( Lemma for ~ irrapx1 .  Explicit description of a non-closed set. $)
    irrapxlem6 $p |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. { y e. QQ | ( 0 < y
        /\ ( abs ` ( y - A ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ( abs ` ( x - A )
        ) < B ) $=
      ( va crp wcel wa cc0 cv clt wbr cmin co cabs cfv cdenom cexp cq wrex cneg
      w3a crab irrapxlem5 simplr simpr1 simpr3 jca weq breq2 oveq1 fveq2d fveq2
      c2 oveq1d breq12d anbi12d elrab sylanbrc simpr2 breq1d rcla4ev syl2anc ex
      rexlimdva mpd ) CFGDFGHZIEJZKLZVHCMNZOPZDKLZVKVHQPZUNUAZRNZKLZUBZESTAJZCM
      NZOPZDKLZAIBJZKLZWBCMNZOPZWBQPZVNRNZKLZHZBSUCZTZECDUDVGVQWKESVGVHSGZHZVQW
      KWMVQHZVHWJGZVLWKWNWLVIVPHZWOVGWLVQUEWNVIVPWMVIVLVPUFWMVIVLVPUGUHWIWPBVHS
      BEUIZWCVIWHVPWBVHIKUJWQWEVKWGVOKWQWDVJOWBVHCMUKULWQWFVMVNRWBVHQUMUOUPUQUR
      USWMVIVLVPUTWAVLAVHWJAEUIZVTVKDKWRVSVJOVRVHCMUKULVAVBVCVDVEVF $.
      $( [13-Sep-2014] $)

    $( Dirichlet's approximation theorem.  Every positive irrational number has
       infinitely many rational approximations which are closer than the
       inverse squares of their reduced denominators.  Lemma 61 in
       [vandenDries] p. 42.  (Contributed by Stefan O'Rear, 14-Sep-2014.) $)
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

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g u $.  $d a b c d e f g v $.  $d a b c d e f g w $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $( a bit of terminology - Pell field = Q[sqr d], Pell ring = Z[sqr d]
       (algebraic integers in Pell field), Pell group = right branch of the
       group of units in Pell ring - isomorphic to ZZ, Pell semigroup = Pell
       group elements >= 1, resembles NN0 $)

    $( Lemma for ~ pellex .  Arithmetical core of pellexlem3, norm lower
       bound.  This begins Dirichlet's proof of the Pell equation solution
       existance; the proof here follows theorem 62 of [vandenDries] p. 43. $)
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
      ( wcel co cabs c2 clt wbr cmul caddc c1 cr cc0 cle syl syl2anc cc syl3anc
      wceq cn w3a cdiv csqr cfv cmin cneg cexp simpl3 resqcl sqge0 absid eqcomd
      wa nnre oveq2d wne simpl2 nncn sqcl simpl1 mulcl subcl nnne0 sqne0 absdiv
      biimpar eqtr4d abscl recnd divcan2 divsubdir syl112anc sqdiv nnnn0 nn0ge0
      remsqsqr resqrcl sqval divcan4 3eqtr4rd oveq12d divcl subsq addcl redivcl
      cn0 resubcl mulcom eqtrd 3eqtrd fveq2d 3eqtr3d absmul remulcl cz nn0negzi
      a1i reexpclz 1re 2re readdcl simpr wb nngt0 divgt0 syl22anc sqrgt0 addgt0
      gt0ne0 absgt0 biimpa ltmul1 mpbid sqgt0 ltmul2 expclz mulass expneg recid
      2nn0 oveq1d mulid2 addcom ppncan 2times recn abstri nn0ge0i sqrge0 mulge0
      3syl nnsqcl nnge1 lt01 lerec ax-1cn div1i eqbrtrd ltletrd syl6breq leadd1
      ltle imp syl21anc letrd ) CUADZAUADZBUADZUBZABUCEZCUDUEZUFEZFUEZBGUGZUHEZ
      HIZUNZAGUHEZCBGUHEZJEZUFEZFUEZUUTUUMUUKUULKEZJEZFUEZJEZLGUULJEZKEZHUURUUT
      UVCUUTUCEZJEZUUTUVBUUTUCEZFUEZJEUVCUVGUURUVJUVMUUTJUURUVJUVCUUTFUEZUCEZUV
      MUURUUTUVNUVCUCUURUVNUUTUURUUTMDZNUUTOIZUVNUUTTUURBMDZUVPUURUUIUVRUUGUUHU
      UIUUQUIZBUOPZBUJPZUURUVRUVQUVTBUKPUUTULQUMUPUURUVBRDZUUTRDZUUTNUQZUVMUVOT
      UURUUSRDZUVARDZUWBUURARDZUWEUURUUHUWGUUGUUHUUIUUQURZAUSPZAUTPZUURCRDZUWCU
      WFUURUUGUWKUUGUUHUUIUUQVAZCUSPZUURBRDZUWCUURUUIUWNUVSBUSPZBUTPZCUUTVBQZUU
      SUVAVCQZUWPUURUWNBNUQZUWDUWOUURUUIUWSUVSBVDPZUWNUWDUWSBVEVGQZUVBUUTVFSVHU
      PUURUVCRDUWCUWDUVKUVCTUURUVCUURUWBUVCMDUWRUVBVIPVJUWPUXAUVCUUTVKSUURUVMUV
      FUUTJUURUVLUVEFUURUVLUUSUUTUCEZUVAUUTUCEZUFEZUUKGUHEZUULGUHEZUFEZUVEUURUW
      EUWFUWCUWDUVLUXDTUWJUWQUWPUXAUUSUVAUUTVLVMUURUXBUXEUXCUXFUFUURUXEUXBUURUW
      GUWNUWSUXEUXBTUWIUWOUWTABVNSUMUURUULUULJEZCUXFUXCUURCMDZNCOIZUXHCTUURUUGU
      XIUWLCUOPZUURCWGDZUXJUURUUGUXLUWLCVOPCVPPZCVQQUURUULRDZUXFUXHTUURUULUURUX
      IUXJUULMDZUXKUXMCVRQZVJZUULVSPUURUWKUWCUWDUXCCTUWMUWPUXACUUTVTSWAWBUURUXG
      UVDUUMJEZUVEUURUUKRDZUXNUXGUXRTUURUWGUWNUWSUXSUWIUWOUWTABWCSZUXQUUKUULWDQ
      UURUVDRDZUUMRDZUXRUVETUURUXSUXNUYAUXTUXQUUKUULWEQZUURUUMUURUUKMDZUXOUUMMD
      ZUURAMDZUVRUWSUYDUURUUHUYFUWHAUOPZUVTUWTABWFSZUXPUUKUULWHQZVJZUVDUUMWIQWJ
      WKWLUPWMUURUVGUUTUUNUVDFUEZJEZJEZUVIHUURUVFUYLUUTJUURUYBUYAUVFUYLTUYJUYCU
      UMUVDWNQUPUURUYMUUTUUPUYKJEZJEZUVIUURUVPUYLMDZUYMMDUWAUURUUNMDZUYKMDZUYPU
      URUYBUYQUYJUUMVIPZUURUYAUYRUYCUVDVIPZUUNUYKWOQZUUTUYLWOQUURUVPUYNMDZUYOMD
      UWAUURUUPMDZUYRVUBUURUVRUWSUUOWPDZVUCUVTUWTVUDUURGYAWQWRZBUUOWSSZUYTUUPUY
      KWOQZUUTUYNWOQUURLMDZUVHMDZUVIMDVUHUURWTWRZUURGMDZUXOVUIVUKUURXAWRZUXPGUU
      LWOQZLUVHXBQZUURUYLUYNHIZUYMUYOHIZUURUUQVUOUUJUUQXCZUURUYQVUCUYRNUYKHIZUU
      QVUOXDUYSVUFUYTUURUYAUVDNUQZVURUYCUURUVDMDZNUVDHIZVUSUURUYDUXOVUTUYHUXPUU
      KUULXBQUURUYDUXONUUKHIZNUULHIZVVAUYHUXPUURUYFNAHIZUVRNBHIZVVBUYGUURUUHVVD
      UWHAXEPUVTUURUUIVVEUVSBXEPABXFXGUURUXINCHIZVVCUXKUURUUGVVFUWLCXEPCXHQUUKU
      ULXIXGUVDXJQUYAVUSVURUVDXKXLQUUNUUPUYKXMVMXNUURUYPVUBUVPNUUTHIZVUOVUPXDVU
      AVUGUWAUURUVRUWSVVGUVTUWTBXOQZUYLUYNUUTXPVMXNUURUYOUYKUVIOUURUYOUUTUUPJEZ
      UYKJEZLUYKJEZUYKUURUWCUUPRDZUYKRDZUYOVVJTUWPUURUWNUWSVUDVVLUWOUWTVUEBUUOX
      QSUURUYKUYTVJZUWCVVLVVMUBVVJUYOUUTUUPUYKXRUMSUURVVILUYKJUURVVIUUTLUUTUCEZ
      JEZLUURUUPVVOUUTJUURUWNGWGDZUUPVVOTUWOVVQUURYAWRBGXSQZUPUURUWCUWDVVPLTUWP
      UXAUUTXTQWJYBUURVVMVVKUYKTVVNUYKYCPWKUURUYKUUMUVHKEZFUEZUVIOUURUVDVVSFUUR
      UVDUULUUKKEZUULUULKEZUUMKEZVVSUURUXSUXNUVDVWATUXTUXQUUKUULYDQUURUXNUXNUXS
      VWAVWCTUXQUXQUXTUXNUXNUXSUBVWCVWAUULUULUUKYEUMSUURVWCUUMVWBKEZVVSUURVWBRD
      ZUYBVWCVWDTUURUXNUXNVWEUXQUXQUULUULWEQUYJVWBUUMYDQUURVWBUVHUUMKUURUXNVWBU
      VHTUXQUXNUVHVWBUULYFUMPUPWJWKWLUURVVTUUNUVHFUEZKEZUVIUURVVSMDZVVSRDVVTMDU
      URUYEVUIVWHUYIVUMUUMUVHXBQVVSYGVVSVIYLUURUYQVWFMDZVWGMDUYSUURUVHRDZVWIUUR
      UVHVUMVJZUVHVIPUUNVWFXBQVUNUURUYBVWJVVTVWGOIUYJVWKUUMUVHYHQUURVWGUUNUVHKE
      ZUVIOUURVWFUVHUUNKUURVUINUVHOIZVWFUVHTVUMUURVUKNGOIZUXONUULOIZVWMVULVWNUU
      RGYAYIWRUXPUURUXIUXJVWOUXKUXMCYJQGUULYKXGUVHULQUPUURUUNLOIZVWLUVIOIZUURUY
      QVUHUUNLHIZVWPUYSVUJUURUUNUUPLUYSVUFVUJVUQUURUUPVVOLOVVRUURVVOLLUCEZLOUUR
      LUUTOIZVVOVWSOIZUURUUTUADZVWTUURUUIVXBUVSBYMPUUTYNPUURVUHNLHIZUVPVVGVWTVX
      AXDVUJVXCUURYOWRUWAVVHLUUTYPXGXNLYQYRUUAYSYTUYQVUHUNVWRVWPUUNLUUCUUDUUEUU
      RUYQVUHVUIVWPVWQXDUYSVUJVUMUUNLUVHUUBSXNYSUUFYSYSYTYSYS $.
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
        va vb csqr wn cneg crab cmul wne c1 caddc copab qex rabex cnumer simprl
        cop simprrl qgt0numnn syl2anc qdencl syl jca simpll pellexlem1 syl31anc
        cdom simplr cdiv simprrr wb qeqnumdivden oveq1d fveq2d mpbid pellexlem2
        breq1d ex weq breq2 oveq1 fveq2 breq12d anbi12d elrab fvex eleq1 anbi1d
        neeq1d anbi2d oveq2d opelopab 3imtr4g ssrab2 sseldi simprr opth oveq12d
        3eqtr4d syl5bi opeq12d impbid1 dom2d mpi ) DEFZDUDGZHFUEZIZJAKZLMZXIXFN
        OZPGZXIQGZRUFZSOZLMZIZAHUGZUAFXRBKZEFZCKZEFZIZXSRSOZDYARSOZUHOZNOZJUIZY
        GPGZUJRXFUHOUKOZLMZIZIZBCULZVGMXQAHUMUNXHUBUCXRYNUBKZUOGZYOQGZUQZUCKZUO
        GZYSQGZUQZUAXHYOHFZJYOLMZYOXFNOZPGZYQXNSOZLMZIZIZYPEFZYQEFZIZYPRSOZDYQR
        SOZUHOZNOZJUIZUUQPGZYJLMZIZIZYOXRFZYRYNFXHUUJUVBXHUUJIZUUMUVAUVDUUKUULU
        VDUUCUUDUUKXHUUCUUIUPZXHUUCUUDUUHURYOUSUTZUVDUUCUULUVEYOVAVBZVCUVDUURUU
        TUVDXEUUKUULXGUURXEXGUUJVDZUVFUVGXEXGUUJVHYPYQDVEVFUVDXEUUKUULYPYQVIOZX
        FNOZPGZUUGLMZUUTUVHUVFUVGUVDUUHUVLXHUUCUUDUUHVJUVDUUCUUHUVLVKUVEUUCUUFU
        VKUUGLUUCUUEUVJPUUCYOUVIXFNYOVLZVMVNVQVBVOYPYQDVPVFVCVCVRXQUUIAYOHAUBVS
        ZXJUUDXPUUHXIYOJLVTUVNXLUUFXOUUGLUVNXKUUEPXIYOXFNWAVNUVNXMYQXNSXIYOQWBV
        MWCWDWEYMUUKYBIZUUNYFNOZJUIZUVPPGZYJLMZIZIUVBBCYPYQYOUOWFZYOQWFZXSYPTZY
        CUVOYLUVTUWCXTUUKYBXSYPEWGWHUWCYHUVQYKUVSUWCYGUVPJUWCYDUUNYFNXSYPRSWAVM
        ZWIUWCYIUVRYJLUWCYGUVPPUWDVNVQWDWDYAYQTZUVOUUMUVTUVAUWEYBUULUUKYAYQEWGW
        JUWEUVQUURUVSUUTUWEUVPUUQJUWEYFUUPUUNNUWEYEUUODUHYAYQRSWAWKWKZWIUWEUVRU
        USYJLUWEUVPUUQPUWFVNVQWDWDWLWMXHUVCYSXRFZIZYRUUBTZUBUCVSZVKZXHUWHIZUUCY
        SHFZUWKUWLXRHYOXQAHWNZXHUVCUWGUPWOUWLXRHYSUWNXHUVCUWGWPWOUUCUWMIZUWIUWJ
        UWIYPYTTZYQUUATZIZUWOUWJYPYQYTUUAUWAUWBYSQWFWQUWOUWRUWJUWOUWRIZUVIYTUUA
        VIOZYOYSUWSYPYTYQUUAVIUWOUWPUWQUPUWOUWPUWQWPWRUWSUUCYOUVITUUCUWMUWRVDUV
        MVBUWSUWMYSUWTTUUCUWMUWRVHYSVLVBWSVRWTUWJYPYTYQUUAYOYSUOWBYOYSQWBXAXBUT
        VRXCXD $.
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
        wss mp2 xpnnen domentr mp2an cdenom cneg crab cdif rpsqrcl anim1i eldif
        nnrp sylibr irrapx1 ensym 3syl pellexlem3 endomtr syl2anc sbth sylancr
        syl ) CEFZCUBGZHFUCZIZAJZEFBJZEFIWCKLMCWDKLMNMUDMZUAUEWEUFGUGKVTNMUHMOP
        IZIABUIZEQPZEWGQPZWGERPWGEEUJZQPZWJERPWHWGUKFWGWJUPWKWGWJEESSULWFABEEUM
        ZUNWLWGWJUKUOUQURWGWJEUSUTWBEUADJZOPWMVTUDMUFGWMVAGKVBLMOPIDHVCZRPZWNWG
        QPWIWBVTTHVDFZWNERPWOWBVTTFZWAIWPVSWQWAVSCTFWQCVHCVEVRVFVTTHVGVIDVTVJWN
        ESVKVLDABCVMEWNWGVNVOWGEVPVQ $.
        $( [14-Sep-2014] $)
    $}

    ${
      $d D x y z $.
      $( Lemma for ~ pellex .  Invoking ~ fiphp3d , we have infinitely many
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
        wss jca32 eldifsn sylanbrc eqeltrd exlimdvv fiphp3d eldif elfzelz simp2
        imp elsn biimpri necon3bi jca syl5 simp2l simp2r cxp mp2 xpnnen domentr
        xpex mp2an ensym rabex weq eqeq1d elrab syl6req 2eximdv 3imtr4g expimpd
        eqtrd ancomsd ssrdv 3adant3 mpsyl endomtr sbth syld reximdv2 mpd ) DFGZ
        DUBHZUCGUDZIZEUEZUFHZJKLZDUWFUGHZJKLZMLZNLZAUEZOZEBUEZFGZCUEZFGZIZUWOJK
        LZDUWQJKLZMLZNLZPUHZUXCUIHZUJJUWCMLZUKLZULQZIZIZBCUTZUMZFUNQZAUXGUOHZUP
        ZUXNUQLZPURZUSZVAUWMPUHZUWSUXCUWMOZIZBCUTZFUNQZIZARVAUWEEAUXKUXRUWLBCDV
        BUXRVCGZUWEUXPVCGUYEUXOUXNVDUXPUXQVEVFVGUWEUWFUXKGZUWLUXRGZUYFUWFUWOUWQ
        VHZOZUXJIZCVLBVLUWEUYGUXJBCUWFVIUWEUYJUYGBCUWEUYJUYGUWEUYJIZUWLUXCUXRUY
        IUWLUXCOUWEUXJUYIUWLUYHUFHZJKLZDUYHUGHZJKLZMLZNLZUXCUYIUWHUYMUWKUYPNUYI
        UWGUYLJKUWFUYHUFVMVJUYIUWJUYODMUYIUWIUYNJKUWFUYHUGVMVJVKVNUYMUWTUYPUXBN
        UYLUWOJKUWOUWQBVOZVPVQUYOUXADMUYNUWQJKUWOUWQUYRCVOVRVQVSVTZWAWBUYKUXCUX
        PGZUXDUXCUXRGUWBUYJUYTUWDUWBUYJIUWSUWBUXHUYTUWBUYIUWSUXIWCUWBUYJWDUXJUX
        HUWBUYIUWSUXDUXHWEWFUWSUWBUXHIZIZUXCRGZUXORGZUXNRGZUXOUXCWGQUXCUXNWGQIZ
        UYTVUBUWTRGZUXBRGZVUCVUBUWORGZVUGUWPVUIUWRVUAUWOWMWHUWOWNSVUBDRGZUXARGZ
        VUHUWBVUJUWSUXHDWMWBVUBUWQRGZVUKVUBUWRVULUWPUWRVUAWIUWQWMSUWQWNSDUXAWJW
        KUWTUXBWLWKZVUBVUEVUDVUBUXGTGZVUEVUBUJTGUXFTGZVUNWOVUBJTGUWCTGZVUOWPVUB
        DTGZPDWGQZVUPUWBVUQUWSUXHDWQWBVUBDWRGZVURUWBVUSUWSUXHDWSWBDWTSDXAWKJUWC
        XBXCUJUXFXDXCZUXGXESZUXNXFSVVAVUBUXCTGZUXNTGZUXEUXNWGQZVUFVUBVUCVVBVUMU
        XCXGSVUBVUEVVCVVAUXNXGSZVUBVVDUXEUXNUJUKLZULQZVUBUXEUXGVVFVUBUXERGZUXET
        GVUBVUCUXEWRGVVHVUMUXCXHUXEXIXJZUXEXGSVUTVUBVVCVVFTGVVEUXNXKSUWSUWBUXHW
        EVUBVUNUXGVVFULQVUTUXGXLSXMVUBVVHVUEVVDVVGYFVVIVVAUXEUXNXNWKXOVVBVVCIVV
        DVUFUXCUXNXPXQXRVUCVUDVUEXSUYTVUFUXCUXOUXNXTYAYBYCYDUXJUXDUWEUYIUWSUXDU
        XHYEWFUXCUXPPUUAUUBUUCYGUUDYHUUIUUEUWEUXMUYDAUXRRUWEUWMUXRGZUXMUWMRGZUY
        DIZUWEVVJVVKUXSIZUXMVVLYIVVJUWMUXPGZUWMUXQGZUDZIUWEVVMUWMUXPUXQUUFUWEVV
        NVVPVVMVVNVVKUWEVVPVVMYIUWMUXOUXNUUGUWEVVKVVPVVMUWEVVKVVPXSVVKUXSUWEVVK
        VVPUUHVVPUWEUXSVVKVVOUWMPVVOUWMPOAPUUJUUKUULYJUUMYKUUNYLYHUWEVVMUXMVVLU
        WEVVMUXMXSZVVKUXSUYCUWEVVKUXSUXMUUOUWEVVKUXSUXMUUPVVQUYBFYMQZFUYBYMQZUY
        CUYBFFUUQZYMQZVVTFUNQVVRUYBYNGUYBVVTYSVWAUYBVVTFFYOYOUVAZUXTBCFFYPZYQVW
        CUYBVVTYNYRUURUUSUYBVVTFUUTUVBVVQFUXLUNQZUXLUYBYMQZVVSUXMUWEVWDVVMUXLFY
        OUVCYJUXLYNGVVQUXLUYBYSZVWEUWNEUXKUXKVVTVWBUXIBCFFYPYQUVDUWEVVMVWFUXMUW
        EVVMIZUAUXLUYBUAUEZUXLGVWHUXKGZVWHUFHZJKLZDVWHUGHZJKLZMLZNLZUWMOZIVWGVW
        HUYBGZUWNVWPEVWHUXKEUAUVEZUWLVWOUWMVWRUWHVWKUWKVWNNVWRUWGVWJJKUWFVWHUFV
        MVJVWRUWJVWMDMVWRUWIVWLJKUWFVWHUGVMVJVKVNUVFUVGVWGVWPVWIVWQVWGVWPVWIVWQ
        VWGVWPIZVWHUYHOZUXJIZCVLBVLVWTUYAIZCVLBVLVWIVWQVWSVXAVXBBCVWSVXAVXBVWSV
        XAIZVWTUWSUXTVWSVWTUXJYEVWSVWTUWSUXIWCVXCUXCVWOUWMVWTUXCVWOOVWSUXJVWTVW
        OUYQUXCVWTVWKUYMVWNUYPNVWTVWJUYLJKVWHUYHUFVMVJVWTVWMUYODMVWTVWLUYNJKVWH
        UYHUGVMVJVKVNUYSUVHWBVWGVWPVXAWIUVLYTYGUVIUXJBCVWHVIUYABCVWHVIUVJUVKUVM
        YHUVNUVOUXLUYBYNYRUVPFUXLUYBUVQWKUYBFUVRXCYTYKUVSYLUVTUWA $.
        $( [19-Oct-2014] $)
    $}

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

        |(A+dB)/(E+dF)| = |(A+dB)(E-dF) / (E+dF)(E-dF)| =
          |(AE-DBF)+d(BE-AF)| / |EE+DFF=C| is the soln
        norm: (AE-DBF)(AE-DBF)-D(BE-AF)(BE-AF) / CC;
        AAEE-2AEDBF+DDBBFF-DBBEE+2DBEAF-DAAFF / CC
        AAEE+DDBBFF-DBBEE-DAAFF / CC
        (AA-DBB)EE-DFF(AA-DBB) / CC
        EE-DFF / C
        1
        divisibility: AE-DBF ~~ AA-DBB ~ C ~ 0 mod C; BE-AF ~~ FE-FE ~ 0
        nontriviality: via the norm, AE-DBF=0 implies d = AF-BE / CC
        contradicting irrationality.  BE-AF=0 means B/A = F/E = r; common norm
        then implies B=A and F=E
      $)


      $( Lemma for ~ pellex .  Doing a field division between near solutions
         get us to norm 1, and the modularity constraint ensures we still have
         an integer.  Returning NN guarantees that we are not returning the
         trivial solution (1,0).  We are not explicitly defining the
         Pell-field, Pell-ring, and Pell-norm explicitly because after this
         construction is done we will never use them.  This is mostly basic
         algebraic number theory and could be simplified if a generic framework
         for that were in place. $)
      pellexlem6 $p |- ( ph -> E. a e. NN E. b e. NN ( ( a ^ 2 ) - ( D x. ( b ^
          2 ) ) ) = 1 ) $=
        ( cmul co cmin cdiv cabs cfv cn wcel c2 cexp c1 wceq cv wrex cz cc0 wne
        cc nncn syl mulcl syl2anc subcl absdiv syl3anc cneg caddc negsub eqcomd
        cmo oveq1d nnre remulcl renegcl nnz modmul1 syl221anc sqcl sqval resqcl
        resubcl 0re a1i abscl divid eqeltrd mod0 mpbird absmod0 3eqtr4d modadd1
        cr wb oveq2d mul12 3eqtrd eqtrd negid mpbid redivcl absz wn cle wbr clt
        cn0 nnnn0 nn0ge0 divcl syl22anc absresq sqdiv syl112anc 3eqtr2d oveq12d
        sqne0 mulsub addcl subdi adddi mulcom mulass sqmul eqtr4d subdir eqtr3d
        wa w3a negeqd 3eqtr3d adantr simpr jca oveq1 divcan1 csqr ad2antrr ex
        zcn crp absrpcl npcan eqtr2d recnd rpne0 1z zre 0mod addid2 zmulcl lt01
        ltnlei mpbi sqge0 mulge0 suble0 breq1 syl5ibrcom mtoi divsubdir nnncan2
        1re divass mul4 addsub4 negsubdi2 mulneg2 fveq2d div0 abs0 syl6eq mtand
        mulneg1 df-ne sylibr divne0 nnabscl nnne0 divmuleq adantl divcan4 nngt0
        sq0 3syl divge0 sqrsq fveq2 sqr1 simplr mulid2 syld sylbird mtod subeq0
        mpd necon3bid eqeq1d rcla42ev ) ABFUCUDZECGUCUDZUCUDZUEUDZDUFUDZUGUHZUI
        UJZCFUCUDZBGUCUDZUEUDZDUFUDZUGUHZUIUJZUXFUKULUDZEUXLUKULUDZUCUDZUEUDZUM
        UNZHUOZUKULUDZEIUOZUKULUDZUCUDZUEUDZUMUNZIUIUPHUIUPAUXEUQUJZUXEURUSZUXG
        AUYFUXFUQUJZAUXFUXDUGUHZDUGUHZUFUDZUQAUXDUTUJZDUTUJZDURUSZUXFUYKUNAUXAU
        TUJZUXCUTUJZUYLABUTUJZFUTUJZUYOABUIUJZUYQJBVAVBZAFUIUJZUYROFVAVBZBFVCVD
        ZAEUTUJZUXBUTUJZUYPAEUIUJZVUDMEVAVBZACUTUJZGUTUJZVUEACUIUJZVUHKCVAVBZAG
        UIUJZVUIPGVAVBZCGVCVDZEUXBVCVDZUXAUXCVEVDZADUQUJZUYMLDUUAVBZRUXDDVFVGAU
        YIUYJVLUDURUNZUYKUQUJZAUXDUYJVLUDZURUNZVUSAVVAURUYJVLUDZURAVVAUXAUXCVHZ
        VIUDZUYJVLUDZUXCVVDVIUDZUYJVLUDZVVCAUXDVVEUYJVLAVVEUXDAUYOUYPVVEUXDUNVU
        CVUOUXAUXCVJVDVKVMAUXAWNUJZUXCWNUJZVVDWNUJZUYJUUBUJZUXAUYJVLUDZUXCUYJVL
        UDZUNVVFVVHUNABWNUJZFWNUJZVVIAUYSVVOJBVNVBZAVUAVVPOFVNVBZBFVOVDZAEWNUJZ
        UXBWNUJZVVJAVUFVVTMEVNVBZACWNUJZGWNUJZVWAAVUJVWCKCVNVBZAVULVWDPGVNVBZCG
        VOVDEUXBVOVDZAVVJVVKVWGUXCVPVBAUYMUYNVVLVURRDUUCVDZAVVMFFUCUDZUYJVLUDZG
        EGUCUDZUCUDZUYJVLUDZVVNAVVOVVPFUQUJZVVLBUYJVLUDFUYJVLUDUNZVVMVWJUNVVQVV
        RAVUAVWNOFVQVBZVWHUABFFUYJVRVSAVWJFUKULUDZEGUKULUDZUCUDZUEUDZVWSVIUDZUY
        JVLUDZURVWSVIUDZUYJVLUDZVWMAVWIVXAUYJVLAVXAVWQVWIAVWQUTUJZVWSUTUJZVXAVW
        QUNAUYRVXEVUBFVTVBZAVUDVWRUTUJZVXFVUGAVUIVXHVUMGVTVBZEVWRVCVDZVWQVWSUUD
        VDAUYRVWQVWIUNVUBFWAVBUUEVMAVWTWNUJZURWNUJZVWSWNUJZVVLVWTUYJVLUDZVVCUNV
        XBVXDUNAVWQWNUJZVXMVXKAVVPVXOVVRFWBVBAVVTVWRWNUJZVXMVWBAVWDVXPVWFGWBVBE
        VWRVOVDZVWQVWSWCVDVXLAWDWEZVXQVWHADUYJVLUDZURVXNVVCAVXSURUNZUYJUYJVLUDU
        RUNZAVYAUYJUYJUFUDZUQUJZAVYBUMUQAUYJUTUJUYJURUSZVYBUMUNAUYJAUYMUYJWNUJZ
        VURDWFVBZUUFAVVLVYDVWHUYJUUGVBUYJWGVDUMUQUJAUUHWEWHAVYEVVLVYAVYCWOVYFVW
        HUYJUYJWIVDWJADWNUJZVVLVXTVYAWOAVUQVYGLDUUIVBZVWHDUYJWKVDWJAVWTDUYJVLTV
        MAVVLVVCURUNVWHUYJUUJVBZWLVWTURVWSUYJWMVSAVXCVWLUYJVLAVXCVWSEGGUCUDZUCU
        DZVWLAVXFVXCVWSUNVXJVWSUUKVBAVWRVYJEUCAVUIVWRVYJUNVUMGWAVBWPAVUDVUIVUIV
        YKVWLUNVUGVUMVUMEGGWQVGWRVMWRAVWMCVWKUCUDZUYJVLUDZVVNAVWDVWCVWKUQUJZVVL
        GUYJVLUDZCUYJVLUDZUNVWMVYMUNVWFVWEAEUQUJZGUQUJZVYNAVUFVYQMEVQVBAVULVYRP
        GVQVBZEGUULVDVWHAVYPVYOUBVKGCVWKUYJVRVSAVYLUXCUYJVLAVUHVUDVUIVYLUXCUNVU
        KVUGVUMCEGWQVGVMWSWRUXAUXCVVDUYJWMVSAVVGURUYJVLAUYPVVGURUNVUOUXCWTVBVMW
        RVYIWSAUXDWNUJZVVLVVBVUSWOAVVIVVJVYTVVSVWGUXAUXCWCVDZVWHUXDUYJWKVDXAAUY
        IWNUJZVVLVUSVUTWOAUYLWUBVUPUXDWFVBVWHUYIUYJWIVDXAWHAUXEWNUJZUYFUYHWOAVY
        TVYGUYNWUCWUAVYHRUXDDXBVGZUXEXCVBWJAUYLUXDURUSZUYMUYNUYGVUPAUXDURUNZXDW
        UEAWUFUMURUXPUEUDZUNZAWUHUMURXEXFZURUMXGXFWUIXDUUMURUMWDUVDUUNUUOAWUIWU
        HWUGURXEXFZAWUJURUXPXEXFZAVVTUREXEXFZUXOWNUJZURUXOXEXFZWUKVWBAEXHUJZWUL
        AVUFWUOMEXIVBEXJVBAUXLWNUJZWUMAUXKUTUJZWUPAUXJUTUJZUYMUYNWUQAUXHUTUJZUX
        IUTUJZWURAVUHUYRWUSVUKVUBCFVCVDZAUYQVUIWUTUYTVUMBGVCVDZUXHUXIVEVDZVURRU
        XJDXKVGUXKWFVBZUXLWBVBZAWUPWUNWVDUXLUUPVBEUXOUUQXLAVXLUXPWNUJZWUJWUKWOV
        XRAVVTWUMWVFVWBWVEEUXOVOVDURUXPUURVDWJUMWUGURXEUUSUUTUVAAWUFYIZUXQUMWUG
        AUXRWUFAUXQUXDUXDUCUDZDUKULUDZUFUDZEUXJUXJUCUDZUCUDZWVIUFUDZUEUDZWVHWVL
        UEUDZWVIUFUDZUMAUXNWVJUXPWVMUEAUXNUXEUKULUDZUXDUKULUDZWVIUFUDZWVJAWUCUX
        NWVQUNWUDUXEXMVBAUYLUYMUYNWVQWVSUNVUPVURRUXDDXNVGAWVRWVHWVIUFAUYLWVRWVH
        UNVUPUXDWAVBVMWRAUXPEUXJUKULUDZWVIUFUDZUCUDZEWVTUCUDZWVIUFUDZWVMAUXOWWA
        EUCAUXOUXKUKULUDZWWAAUXKWNUJZUXOWWEUNAUXJWNUJZVYGUYNWWFAUXHWNUJZUXIWNUJ
        ZWWGAVWCVVPWWHVWEVVRCFVOVDZAVVOVWDWWIVVQVWFBGVOVDZUXHUXIWCVDZVYHRUXJDXB
        VGZUXKXMVBAWURUYMUYNWWEWWAUNWVCVURRUXJDXNVGWSWPAVUDWVTUTUJZWVIUTUJZWVIU
        RUSZWWDWWBUNVUGAWURWWNWVCUXJVTVBAUYMWWOVURDVTVBZAWWPUYNRAUYMWWPUYNWOVUR
        DXRVBWJZEWVTWVIUVEXOAWWCWVLWVIUFAWVTWVKEUCAWURWVTWVKUNWVCUXJWAVBWPVMXPX
        QAWVHUTUJZWVLUTUJZWWOWWPWVPWVNUNAUYLUYLWWSVUPVUPUXDUXDVCVDAVUDWVKUTUJZW
        WTVUGAWURWURWXAWVCWVCUXJUXJVCVDEWVKVCVDWWQWWRWVHWVLWVIUVBXOAWVPUXAUXAUC
        UDZUXCUXCUCUDZVIUDZUXAUXCUCUDZWXEVIUDZUEUDZEUXHUXHUCUDZUCUDZEUXIUXIUCUD
        ZUCUDZVIUDZEUXHUXIUCUDZUCUDZWXNVIUDZUEUDZUEUDZWVIUFUDWVIWVIUFUDZUMAWVOW
        XQWVIUFAWVHWXGWVLWXPUEAUYOUYPUYOUYPWVHWXGUNVUCVUOVUCVUOUXAUXCUXAUXCXSXL
        AWVLEWXHWXJVIUDZWXMWXMVIUDZUEUDZUCUDZEWXSUCUDZEWXTUCUDZUEUDZWXPAWVKWYAE
        UCAWUSWUTWUSWUTWVKWYAUNWVAWVBWVAWVBUXHUXIUXHUXIXSXLWPAVUDWXSUTUJZWXTUTU
        JZWYBWYEUNVUGAWXHUTUJZWXJUTUJZWYFAWUSWUSWYHWVAWVAUXHUXHVCVDZAWUTWUTWYIW
        VBWVBUXIUXIVCVDZWXHWXJXTVDAWXMUTUJZWYLWYGAWUSWUTWYLWVAWVBUXHUXIVCVDZWYM
        WXMWXMXTVDEWXSWXTYAVGAWYCWXLWYDWXOUEAVUDWYHWYIWYCWXLUNVUGWYJWYKEWXHWXJY
        BVGAVUDWYLWYLWYDWXOUNVUGWYMWYMEWXMWXMYBVGXQWRXQVMAWXQWVIWVIUFAWXQWXDWXO
        UEUDZWXPUEUDZWXDWXLUEUDZWVIAWXGWYNWXPUEAWXFWXOWXDUEAWXEWXNWXEWXNVIAWXEU
        XCUXAUCUDZEUXBUXAUCUDZUCUDZWXNAUYOUYPWXEWYQUNVUCVUOUXAUXCYCVDAVUDVUEUYO
        WYQWYSUNVUGVUNVUCEUXBUXAYDVGAWYRWXMEUCAWYRUXBFBUCUDZUCUDZUXHGBUCUDZUCUD
        ZWXMAUXAWYTUXBUCAUYQUYRUXAWYTUNUYTVUBBFYCVDWPAVUHVUIUYRUYQXUAXUCUNVUKVU
        MVUBUYTCGFBUVFXLAXUBUXIUXHUCAVUIUYQXUBUXIUNVUMUYTGBYCVDWPWRWPWRZXUDXQWP
        VMAWXDUTUJZWXLUTUJZWXOUTUJZWYOWYPUNAWXBUTUJZWXCUTUJZXUEAUYOUYOXUHVUCVUC
        UXAUXAVCVDZAUYPUYPXUIVUOVUOUXCUXCVCVDZWXBWXCXTVDAWXIUTUJZWXKUTUJZXUFAVU
        DWYHXULVUGWYJEWXHVCVDZAVUDWYIXUMVUGWYKEWXJVCVDZWXIWXKXTVDAWXNUTUJZXUPXU
        GAVUDWYLXUPVUGWYMEWXMVCVDZXUQWXNWXNXTVDWXDWXLWXOUVCVGAWYPWXBWXIUEUDZWXC
        WXKUEUDZVIUDZUXAUKULUDZEUXHUKULUDZUCUDZUEUDZUXCUKULUDZEUXIUKULUDZUCUDZU
        EUDZVIUDZWVIAXUHXUIXULXUMWYPXUTUNXUJXUKXUNXUOWXBWXCWXIWXKUVGXLAXVDXURXV
        HXUSVIAXVAWXBXVCWXIUEAUYOXVAWXBUNVUCUXAWAVBAXVBWXHEUCAWUSXVBWXHUNWVAUXH
        WAVBWPXQAXVEWXCXVGWXKUEAUYPXVEWXCUNVUOUXCWAVBAXVFWXJEUCAWUTXVFWXJUNWVBU
        XIWAVBWPXQXQAXVIBUKULUDZVWQUCUDZECUKULUDZUCUDZVWQUCUDZUEUDZEEUCUDZXVLUC
        UDZVWRUCUDZEXVJUCUDZVWRUCUDZUEUDZVIUDDVWQUCUDZEDUCUDZVHZVWRUCUDZVIUDZWV
        IAXVDXVOXVHXWAVIAXVAXVKXVCXVNUEAUYQUYRXVAXVKUNUYTVUBBFYEVDAXVCEXVLVWQUC
        UDZUCUDZXVNAXVBXWGEUCAVUHUYRXVBXWGUNVUKVUBCFYEVDWPAVUDXVLUTUJZVXEXVNXWH
        UNVUGAVUHXWIVUKCVTVBZVXGEXVLVWQYDVGYFXQAXVEXVRXVGXVTUEAEUKULUDZUXBUKULU
        DZUCUDZXVPXVLVWRUCUDZUCUDZXVEXVRAXWKXVPXWLXWNUCAVUDXWKXVPUNVUGEWAVBAVUH
        VUIXWLXWNUNVUKVUMCGYEVDXQAVUDVUEXVEXWMUNVUGVUNEUXBYEVDAXVPUTUJZXWIVXHXV
        RXWOUNAVUDVUDXWPVUGVUGEEVCVDZXWJVXIXVPXVLVWRYDVGWLAXVGEXVJVWRUCUDZUCUDZ
        XVTAXVFXWREUCAUYQVUIXVFXWRUNUYTVUMBGYEVDWPAVUDXVJUTUJZVXHXVTXWSUNVUGAUY
        QXWTUYTBVTVBZVXIEXVJVWRYDVGYFXQXQAXVOXWBXWAXWEVIAXVJXVMUEUDZVWQUCUDZXVO
        XWBAXWTXVMUTUJZVXEXXCXVOUNXXAAVUDXWIXXDVUGXWJEXVLVCVDZVXGXVJXVMVWQYGVGA
        XXBDVWQUCSVMYHAXVQXVSUEUDZVWRUCUDZEXVMUCUDZXVSUEUDZVWRUCUDXWAXWEAXXFXXI
        VWRUCAXVQXXHXVSUEAVUDVUDXWIXVQXXHUNVUGVUGXWJEEXVLYDVGVMVMAXVQUTUJZXVSUT
        UJZVXHXXGXWAUNAXWPXWIXXJXWQXWJXVPXVLVCVDAVUDXWTXXKVUGXXAEXVJVCVDVXIXVQX
        VSVWRYGVGAXXIXWDVWRUCAXXIEXVMXVJUEUDZUCUDZEDVHZUCUDZXWDAVUDXXDXWTXXIXXM
        UNVUGXXEXXAVUDXXDXWTYJXXMXXIEXVMXVJYAVKVGAXXLXXNEUCAXXLXXBVHZXXNAXWTXXD
        XXLXXPUNXXAXXEXWTXXDYIXXPXXLXVJXVMUVHVKVDAXXBDSYKWSWPAVUDUYMXXOXWDUNVUG
        VUREDUVIVDWRVMYLXQAXWFXWBDVWSUCUDZVHZVIUDZXWBXXQUEUDZWVIAXWEXXRXWBVIAXW
        EXWCVWRUCUDZVHZXXRAXWCUTUJZVXHXWEXYBUNAVUDUYMXYCVUGVUREDVCVDVXIXWCVWRUV
        OVDAXYAXXQAXYADEUCUDZVWRUCUDZXXQAXWCXYDVWRUCAVUDUYMXWCXYDUNVUGVUREDYCVD
        VMAUYMVUDVXHXYEXXQUNVURVUGVXIDEVWRYDVGWSYKWSWPAXWBUTUJZXXQUTUJZXXSXXTUN
        AUYMVXEXYFVURVXGDVWQVCVDAUYMVXFXYGVURVXJDVWSVCVDXWBXXQVJVDADVWTUCUDZDDU
        CUDZXXTWVIAVWTDDUCTWPAUYMVXEVXFXXTXYHUNVURVXGVXJUYMVXEVXFYJXYHXXTDVWQVW
        SYAVKVGAUYMWVIXYIUNVURDWAVBWLWRWRXPWRVMAWWOWWPWXRUMUNWWQWWRWVIWGVDWRXPZ
        YMWVGUXNURUXPUEWVGUXNURUKULUDURWVGUXFURUKULWVGUXFURDUFUDZUGUHZURWVGUXEX
        YKUGWVGUXDURDUFAWUFYNVMUVJAXYLURUNWUFAXYLURUGUHURAXYKURUGAUYMUYNXYKURUN
        VURRDUVKVDUVJUVLUVMYMWSVMUWEUVMVMYHUVNUXDURUVPUVQVURRUXDDUVRXLUXEUVSVDA
        UXKUQUJZUXKURUSZUXMAXYMUXLUQUJZAUXLUXJUGUHZUYJUFUDZUQAWURUYMUYNUXLXYQUN
        WVCVURRUXJDVFVGAXYPUYJVLUDURUNZXYQUQUJZAUXJUYJVLUDZURUNZXYRAXYTVVCURAXY
        TUXHUXIVHZVIUDZUYJVLUDZUXIYUBVIUDZUYJVLUDZVVCAUXJYUCUYJVLAWUSWUTUXJYUCU
        NWVAWVBWUSWUTYIYUCUXJUXHUXIVJVKVDVMAWWHWWIYUBWNUJZVVLUXHUYJVLUDZUXIUYJV
        LUDZUNYUDYUFUNWWJWWKAWWIYUGWWKUXIVPVBVWHAGFUCUDZUYJVLUDZFGUCUDZUYJVLUDZ
        YUHYUIAYUJYULUYJVLAVUIUYRYUJYULUNVUMVUBGFYCVDVMAVWCVWDVWNVVLVYPVYOUNYUH
        YUKUNVWEVWFVWPVWHUBCGFUYJVRVSAVVOVVPVYRVVLVWOYUIYUMUNVVQVVRVYSVWHUABFGU
        YJVRVSWLUXHUXIYUBUYJWMVSAYUEURUYJVLAWUTYUEURUNWVBUXIWTVBVMWRVYIWSAWWGVV
        LYUAXYRWOWWLVWHUXJUYJWKVDXAAXYPWNUJZVVLXYRXYSWOAWURYUNWVCUXJWFVBVWHXYPU
        YJWIVDXAWHAWWFXYMXYOWOWWMUXKXCVBWJAWURUXJURUSZUYMUYNXYNWVCAYUOUXHUXIUSZ
        AUXHUXIUNZXDYUPAYUQBFUNZCGUNZYIZQAYUQCGUFUDZBFUFUDZUNZYUTAVUHUYQVUIGURU
        SZYIUYRFURUSZYIYVCYUQWOVUKUYTAVUIYVDVUMAVULYVDPGUVTVBZYOAUYRYVEVUBAVUAY
        VEOFUVTVBZYOCBGFUWAXLAYVCYUTAYVCYIZYVAUKULUDZUMUNZYUTYVHYVIDUCUDZDUFUDZ
        XXBXXBUFUDZYVIUMYVHYVKXXBDXXBUFYVHYVKYVIVWTUCUDZYVIVWQUCUDZYVIVWSUCUDZU
        EUDZXXBYVHDVWTYVIUCYVHVWTDAVWTDUNYVCTYMVKWPYVHYVIUTUJZVXEVXFYVNYVQUNAYV
        RYVCAYVAUTUJZYVRAVUHVUIYVDYVSVUKVUMYVFCGXKVGYVAVTVBYMZAVXEYVCVXGYMZAVXF
        YVCVXJYMYVIVWQVWSYAVGYVHYVOXVJYVPXVMUEYVHYVOYVBUKULUDZVWQUCUDZXVJVWQUFU
        DZVWQUCUDZXVJYVCYVOYWCUNAYVCYVIYWBVWQUCYVAYVBUKULYPVMUWBYVHYWBYWDVWQUCY
        VHUYQUYRYVEYWBYWDUNAUYQYVCUYTYMAUYRYVCVUBYMAYVEYVCYVGYMBFXNVGVMYVHXWTVX
        EVWQURUSZYWEXVJUNAXWTYVCXXAYMYWAAYWFYVCAYWFYVEYVGAUYRYWFYVEWOVUBFXRVBWJ
        YMXVJVWQYQVGWRYVHYVPEYVIVWRUCUDZUCUDZEXVLVWRUFUDZVWRUCUDZUCUDXVMYVHYVRV
        UDVXHYVPYWHUNYVTAVUDYVCVUGYMAVXHYVCVXIYMZYVIEVWRWQVGYVHYWGYWJEUCYVHYVIY
        WIVWRUCYVHVUHVUIYVDYVIYWIUNAVUHYVCVUKYMAVUIYVCVUMYMAYVDYVCYVFYMCGXNVGVM
        WPYVHYWJXVLEUCYVHXWIVXHVWRURUSZYWJXVLUNAXWIYVCXWJYMYWKAYWLYVCAYWLYVDYVF
        AVUIYWLYVDWOVUMGXRVBWJYMXVLVWRYQVGWPWRXQWRADXXBUNYVCAXXBDSVKYMXQYVHYVRU
        YMUYNYVLYVIUNYVTAUYMYVCVURYMAUYNYVCRYMYVIDUWCVGAYVMUMUNYVCAYVMDDUFUDZUM
        AXXBDXXBDUFSSXQAUYMUYNYWMUMUNVURRDWGVDWSYMYLYVHYVJYVAUMUNZYUTYVHYVJYWNY
        VHYVJYIZYVAYVIYRUHZUMYRUHZUMAYVAYWPUNYVCYVJAYWPYVAAYVAWNUJZURYVAXEXFZYW
        PYVAUNAVWCVWDYVDYWRVWEVWFYVFCGXBVGAVWCURCXEXFZVWDURGXGXFZYWSVWEAVUJCXHU
        JYWTKCXICXJUWFVWFAVULYXAPGUWDVBCGUWGXLYVAUWHVDVKYSYVJYWPYWQUNYVHYVIUMYR
        UWIUWBYWQUMUNYWOUWJWEWRYTYVHYWNYUTYVHYWNYIZYURYUSYXBYVBFUCUDZUMFUCUDZBF
        YXBYVBUMFUCYXBYVAYVBUMAYVCYWNUWKYVHYWNYNZYHVMAYXCBUNZYVCYWNAUYQUYRYVEYX
        FUYTVUBYVGBFYQVGYSAYXDFUNZYVCYWNAUYRYXGVUBFUWLVBYSYLYXBYVAGUCUDZUMGUCUD
        ZCGYXBYVAUMGUCYXEVMAYXHCUNZYVCYWNAVUHVUIYVDYXJVUKVUMYVFCGYQVGYSAYXIGUNZ
        YVCYWNAVUIYXKVUMGUWLVBYSYLYOYTUWMUWQYTUWNUWOUXHUXIUVPUVQAUXJURUXHUXIAWU
        SWUTUXJURUNYUQWOWVAWVBUXHUXIUWPVDUWRWJVURRUXJDUVRXLUXKUVSVDXYJUYEUXRUXN
        UYCUEUDZUMUNHIUXFUXLUIUIUXSUXFUNZUYDYXLUMYXMUXTUXNUYCUEUXSUXFUKULYPVMUW
        SUYAUXLUNZYXLUXQUMYXNUYCUXPUXNUEYXNUYBUXOEUCUYAUXLUKULYPWPWPUWSUWTVG $.
        $( [19-Oct-2014] $)
    $}

    ${
      $d D x y $.
      $( Every Pell equation has a nontrivial solution.  Theorem 62 in
         [vandenDries] p. 43.  (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
      pellex $p |- ( ( D e. NN /\ -. ( sqr ` D ) e. QQ ) -> E. x e. NN E. y e.
          NN ( ( x ^ 2 ) - ( D x. ( y ^ 2 ) ) ) = 1 ) $=
        ( vb vc vf vg cn wcel cfv wa cv c2 cexp co wceq wbr c1st cmo c2nd va vd
        ve csqr cq wn cc0 wne cmul cmin copab cen cz wrex c1 pellexlem5 cop cfz
        cabs cxp cvv csdm nnex xpex opabssxp ssexi simprr syl com cfn fzfi xpfi
        ensym mp2an isfinite3 mpbi omex nnenom ensymi pm3.2i sdomentr mp2 jctil
        mpsyl sseli simprrl simpllr simplr nnabscl syl2anc zmodfz simprrr elxp7
        nnz jca ex ovex opelxp 3imtr4g syl5 imp adantlrr weq fveq2 oveq1d fphpd
        opeq12d wi eleq1 bi2anan9 oveq1 oveq2d oveqan12d eqeq1d cbvopabv eleq2i
        anbi12d biimpi wex elopab w3a simp3ll 3expb 3ad2ant1 ad3antrrr 3adant2l
        simp1lr simp3 vex opth sylib syl3anc fveq2d op1st syl6eq op2nd exlimdvv
        3eqtr3d mpd syl5bi simp3lr 3adant1r simpl simpr simp2ll simp2lr simp1rl
        simp2l simp3l 3netr3d necon3abii simp1rr 3adant1l simp2rr simp3r simprl
        simp2 simp1 simpll 3adant3 simpld simprd pellexlem6 imp3a sylan2i mpdan
        3exp rexlimdvv rexlimdva ) CHIZCUDJUEIUFZKZUALZUGUHZDLZHIZELZHIZKZUVOMN
        OZCUVQMNOZUIOZUJOZUVMPZKZDEUKZHULQZKZUAUMUNALMNOCBLMNOUIOUJOUOPBHUNAHUN
        ZUADECUPUVLUWHUWIUAUMUVLUVMUMIZKZUWHUWIUWKUWHKZUBLZUCLZUHZUWMRJZUVMUSJZ
        SOZUWMTJZUWQSOZUQZUWNRJZUWQSOZUWNTJZUWQSOZUQZPZKZUCUWFUNUBUWFUNZUWIUWLU
        BUCUWFUGUWQUOUJOZUROZUXKUTZUXAUXFUWFVAIUWLUXLHVBQZHUWFULQZKUXLUWFVBQUWF
        HHUTZHHVCVCVDUWDDEHHVEZVFUWLUXNUXMUWLUWGUXNUWKUVNUWGVGUWFHVCVMVHHVAIUXL
        VIVBQZVIHULQZKUXMVCUXQUXRUXLVJIZUXQUXKVJIZUXTUXSUGUXJVKZUYAUXKUXKVLVNUX
        LVOVPHVIVQVRVSVTUXLVIHVAWAWBWCUXLHUWFVAWAWDUWKUVNUWMUWFIZUXAUXLIZUWGUWK
        UVNKZUYBUYCUYBUWMUXOIZUYDUYCUWFUXOUWMUXPWEUYDUWMVAVAUTIZUWPHIZUWSHIZKKZ
        UWRUXKIZUWTUXKIZKZUYEUYCUYDUYIUYLUYDUYIKZUYJUYKUYMUWPUMIZUWQHIZUYJUYMUY
        GUYNUYDUYFUYGUYHWFUWPWNVHUYMUWJUVNUYOUVLUWJUVNUYIWGUWKUVNUYIWHUVMWIWJZU
        WPUWQWKWJUYMUWSUMIZUYOUYKUYMUYHUYQUYDUYFUYGUYHWLUWSWNVHUYPUWSUWQWKWJWOW
        PUWMHHWMUWRUWTUXKUXKUWSUWQSWQZWRWSWTXAXBUBUCXCZUWRUXCUWTUXEUYSUWPUXBUWQ
        SUWMUWNRXDXEUYSUWSUXDUWQSUWMUWNTXDXEXGXFUWKUVNUXIUWIUWGUYDUXIUWIUYDUXHU
        WIUBUCUWFUWFUWNUWFIZUYDUYBUWNFLZHIZGLZHIZKZVUAMNOZCVUCMNOZUIOZUJOZUVMPZ
        KZFGUKZIZUXHUWIXHZUYTVUMUWFVULUWNUWEVUKDEFGDFXCZEGXCZKZUVSVUEUWDVUJVUOU
        VPVUBVUPUVRVUDUVOVUAHXIUVQVUCHXIXJVUQUWCVUIUVMVUOVUPUVTVUFUWBVUHUJUVOVU
        AMNXKVUPUWAVUGCUIUVQVUCMNXKXLXMXNXQXOXPXRUYDUYBVUMVUNUYBUWMUVOUVQUQZPZU
        WEKZEXSDXSUYDVUMVUNXHZUWEDEUWMXTUYDVUTVVADEUYDVUTVVAVUMUWNVUAVUCUQZPZVU
        KKZGXSFXSUYDVUTKZVUNVUKFGUWNXTVVEVVDVUNFGVVEVVDUXHUWIVVEVVDUXHYAZUVOUVQ
        UVMCVUAVUCABVVEVVDUVPUXHUYDVUSUWEUVPUVPUVRUWDUYDVUSYBYCYDVVEVVDUVRUXHUY
        DVUSUWEUVRUVPUVRUWDUYDVUSUUAYCYDUYDVVDUXHUWJVUTUVLUWJUVNVVDUXHYGUUBVVEV
        VDUVJUXHUVLUVJUWJUVNVUTUVJUVKUUCYEYDVVEVVDUVKUXHUVLUVKUWJUVNVUTUVJUVKUU
        DYEYDVVEVUKUXHVUBVVCVUBVUDVUJVVEUXHUUEYFVVEVUKUXHVUDVVCVUBVUDVUJVVEUXHU
        UFYFVVFVVCVUSUWOVUQUFZVVEVVCVUKUXHUUHZVUSUWEUYDVVDUXHUUGZVVEVVDUWOUXGUU
        IVVCVUSUWOYAZVURVVBUHVVGVVJUWMUWNVURVVBVVCVUSUWOYHVVCVUSUWOUUQVVCVUSUWO
        UURUUJVUQVURVVBUVOUVQVUAVUCDYIZEYIZGYIZYJUUKYKYLUWKUVNVUTVVDUXHYGVUTVVD
        UXHUWDUYDUVSUWDVUSVVDUXHUULUUMVUEVUJVVCVVEUXHUUNVVFUVOUWQSOZVUAUWQSOZPZ
        UVQUWQSOZVUCUWQSOZPZVVFVUSVVCUXGVVPVVSKZVVIVVHVVEVVDUWOUXGUUOVUSVVCUXGY
        AZUWRUXCPZUWTUXEPZKZVVTVWAUXGVWDVUSVVCUXGYHUWRUWTUXCUXEUWPUWQSWQUYRUXDU
        WQSWQYJYKVUSVVCVWDVVTXHUXGVUSVVCKZVWDVVTVWEVWDKZVVPVVSVWFUWRUXCVVNVVOVW
        EVWBVWCUUPVWFUWPUVOUWQSVWFUWPVURRJUVOVWFUWMVURRVUSVVCVWDUUSZYMUVOUVQVVK
        YNYOXEVWFUXBVUAUWQSVWFUXBVVBRJVUAVWFUWNVVBRVUSVVCVWDWHZYMVUAVUCFYIZYNYO
        XEYRVWFUWTUXEVVQVVRVWEVWBVWCVGVWFUWSUVQUWQSVWFUWSVURTJUVQVWFUWMVURTVWGY
        MUVOUVQVVKVVLYPYOXEVWFUXDVUCUWQSVWFUXDVVBTJVUCVWFUWNVVBTVWHYMVUAVUCVWIV
        VMYPYOXEYRWOWPUUTYSYLZUVAVVFVVPVVSVWJUVBUVCUVGYQYTWPYQYTUVDUVEUVHXAXBUV
        FWPUVIYS $.
        $( [19-Oct-2014] $)
    $}
  $}

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

    $( define image of ZZ or NN $)
    $( prove non-denseness $)
    $( use logarithms to show all elements are powers of a base $)
    $( value of PellFund ` a*a-1 $)
    $( define Ak, Bk $)
    $( Lucas sequence $)

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
      $( Value of the set of first-quadrant Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
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

      $( Membership in a first-quadrant Pell solution set.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      elpell1qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e.
          RR /\ E. z e. NN0 E. w e. NN0 ( A = ( z + ( ( sqr ` D ) x. w ) ) /\ (
          ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn cdif wcel cfv cv cmul co wceq c2 cexp wa cn0 wrex cr
        cpell1qr csqr caddc cmin c1 crab pell1qrval eleq2d eqeq1 2rexbidv elrab
        anbi1d syl6bb ) DFGHIZCDUAJZICEKZAKZDUBJBKZLMUCMZNZUQOPMDUROPMLMUDMUENZ
        QZBRSARSZETUFZICTICUSNZVAQZBRSARSZQUNUOVDCEABDUGUHVCVGECTUPCNZVBVFABRRV
        HUTVEVAUPCUSUIULUJUKUM $.
        $( [17-Sep-2014] $)

      $( Value of the set of positive Pell solutions.  (Contributed by Stefan
         O'Rear, 17-Sep-2014.) $)
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

      $( Membership in the set of positive Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      elpell14qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A
          e. RR /\ E. z e. NN0 E. w e. ZZ ( A = ( z + ( ( sqr ` D ) x. w ) ) /\
          ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn wcel cfv cv cmul co wceq c2 cexp wa cz wrex cn0 cr c1
        cdif cpell14qr csqr caddc cmin pell14qrval eleq2d eqeq1 anbi1d 2rexbidv
        crab elrab syl6bb ) DFGUBHZCDUCIZHCEJZAJZDUDIBJZKLUELZMZURNOLDUSNOLKLUF
        LUAMZPZBQRASRZETULZHCTHCUTMZVBPZBQRASRZPUOUPVECEABDUGUHVDVHECTUQCMZVCVG
        ABSQVIVAVFVBUQCUTUIUJUKUMUN $.
        $( [17-Sep-2014] $)

      $( Value of the set of general Pell solutions.  (Contributed by Stefan
         O'Rear, 17-Sep-2014.) $)
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

      $( Membership in the set of general Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
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

    $( General Pell solutions are (coded as) real numbers.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
    pell1234qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> A
        e. RR ) $=
      ( va vb cn csquarenn cdif wcel cpell1234qr cfv cr cv csqr cmul co wceq c2
      cexp cz wrex caddc cmin c1 wa elpell1234qr simprbda ) BEFGHABIJHAKHACLZBM
      JDLZNOUAOPUGQROBUHQRONOUBOUCPUDDSTCSTCDABUEUF $.
      $( [17-Sep-2014] $)

    $( No solution to a Pell equation is zero.  (Contributed by Stefan O'Rear,
       17-Sep-2014.) $)
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

    $( General solutions of the Pell equation are closed under reciprocals.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) )
        -> ( 1 / A ) e. ( Pell1234QR ` D ) ) $=
      ( vc vd va wcel wa c1 co cmul caddc wceq c2 cexp cz syl2anc syl cc oveq2d
      cmin vb cn csquarenn cdif cpell1234qr cdiv cr cv csqr elpell1234qr biimpa
      cfv wrex cc0 wne pell1234qrre pell1234qrne0 rereccl ad2antrr cneg simplrl
      simplrr znegcl eldifi nncn ad3antrrr sqrcl zcn sqmul oveq1d eqtr2d simprr
      sqrth adantr ad2antlr mulcl subsq 3eqtr3d recnd recid simprl negsub eqtrd
      mulneg2 oveq12d 3eqtr4d wb negcl addcl mulcan syl112anc mpbid sqneg oveq1
      weq eqeq2d eqeq1d anbi12d oveq2 rcla42ev jca ex rexlimdvva adantld mpbird
      mpd ) BUBUCUDFZABUEULZFZGZHAUFIZXHFZXKUGFZXKCUHZBUIULZDUHZJIZKIZLZXNMNIZB
      XPMNIZJIZTIZHLZGZDOUMCOUMZGZXJAUGFZAEUHZXOUAUHZJIZKIZLZYIMNIZBYJMNIZJIZTI
      ZHLZGZUAOUMEOUMZGZYGXGXIUUAEUAABUJUKXJYTYGYHXJYSYGEUAOOXJYIOFZYJOFZGZGZYS
      YGUUEYSGZXMYFXJXMUUDYSXJYHAUNUOZXMABUPZABUQZAURPZUSUUFUUBYJUTZOFZXKYIXOUU
      KJIZKIZLZYNBUUKMNIZJIZTIZHLZYFXJUUBUUCYSVAUUFUUCUULXJUUBUUCYSVBZYJVCQUUFA
      XKJIZAUUNJIZLZUUOUUFHYLYIYKTIZJIZUVAUVBUUFYQYNYKMNIZTIZHUVEUUFYPUVFYNTUUF
      UVFXOMNIZYOJIZYPUUFXORFZYJRFZUVFUVILUUFBRFZUVJXGUVLXIUUDYSXGBUBFUVLBUBUCV
      DBVEQVFZBVGQZUUFUUCUVKUUTYJVHQZXOYJVIPUUFUVHBYOJUUFUVLUVHBLUVMBVMQVJVKSUU
      EYMYRVLZUUFYIRFZYKRFZUVGUVELUUDUVQXJYSUUBUVQUUCYIVHVNVOZUUFUVJUVKUVRUVNUV
      OXOYJVPPZYIYKVQPVRUUFARFZUUGUVAHLXJUWAUUDYSXJAUUHVSUSZXJUUGUUDYSUUIUSZAVT
      PUUFAYLUUNUVDJUUEYMYRWAUUFUUNYIYKUTZKIZUVDUUFUUMUWDYIKUUFUVJUVKUUMUWDLUVN
      UVOXOYJWDPSUUFUVQUVRUWEUVDLUVSUVTYIYKWBPWCWEWFUUFXKRFZUUNRFZUWAUUGUVCUUOW
      GXJUWFUUDYSXJXKUUJVSUSUUFUVQUUMRFZUWGUVSUUFUVJUUKRFZUWHUVNUUFUVKUWIUVOYJW
      HQXOUUKVPPYIUUMWIPUWBUWCXKUUNAWJWKWLUUFUURYQHUUFUUQYPYNTUUFUUPYOBJUUFUVKU
      UPYOLUVOYJWMQSSUVPWCYEUUOUUSGXKYIXQKIZLZYNYBTIZHLZGCDYIUUKOOCEWOZXSUWKYDU
      WMUWNXRUWJXKXNYIXQKWNWPUWNYCUWLHUWNXTYNYBTXNYIMNWNVJWQWRXPUUKLZUWKUUOUWMU
      USUWOUWJUUNXKUWOXQUUMYIKXPUUKXOJWSSWPUWOUWLUURHUWOYBUUQYNTUWOYAUUPBJXPUUK
      MNWNSSWQWRWTWKXAXBXCXDXFXGXLYGWGXICDXKBUJVNXE $.
      $( [18-Sep-2014] $)

    $( General solutions of the Pell equation are closed under multiplication.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) /\
        B e. ( Pell1234QR ` D ) ) -> ( A x. B ) e. ( Pell1234QR ` D ) ) $=
      ( wcel cmul co wa caddc wceq c2 cexp cmin c1 cz ad3antrrr syl2anc oveq12d
      cc mulcl oveq2d va vb vc vd ve vf cn csquarenn cdif cpell1234qr cfv cr cv
      csqr wrex simplr remulcl syl simprl simplrl zmulcl simpll eldifi nnz 3syl
      wi simplrr simprr zaddcl ad2antrr zcn ad2antrl nncn sqrcl ad2antll adantr
      ad2antlr adantl muladd mul4 sqval sqrth eqtr3d oveq1d eqtrd mul12 syl3anc
      syl22anc adddi eqcomd 3eqtrd addcl sqmul eqtr2d subsq mulsub subcl ax-1cn
      mulid2i a1i jca oveq1 eqeq2d eqeq1d anbi12d oveq2 rexlimdvva elpell1234qr
      rcla42ev ex imp3a an4 syl6bb 3imtr4d 3impib ) CUGUHUIDZACUJUKZDZBXQDZABEF
      ZXQDZXPAULDZBULDZGZAUAUMZCUNUKZUBUMZEFZHFZIZYEJKFZCYGJKFZEFZLFZMIZGZUBNUO
      UANUOZBUCUMZYFUDUMZEFZHFZIZYRJKFZCYSJKFZEFZLFZMIZGZUDNUOUCNUOZGZGZXTULDZX
      TUEUMZYFUFUMZEFZHFZIZUUMJKFZCUUNJKFZEFZLFZMIZGZUFNUOUENUOZGZXRXSGZYAXPYDU
      UJUVEXPYDUUJUVEVFXPYDGZYQUUIUVEUVGYPUUIUVEVFZUAUBNNUVGYENDZYGNDZGZGZYPUVH
      UVLYPGZUUHUVEUCUDNNUVMYRNDZYSNDZGZGZUUHUVEUVQUUHGZUULUVDUVRYDUULUVLYDYPUV
      PUUHXPYDUVKUPOABUQURUVRYEYREFZCYSYGEFZEFZHFZNDZYEYSEFZYRYGEFZHFZNDZXTUWBY
      FUWFEFZHFZIZUWBJKFZCUWFJKFZEFZLFZMIZGZUVDUVRUVSNDZUWANDZUWCUVRUVIUVNUWQUV
      LUVIYPUVPUUHUVGUVIUVJUSOZUVMUVNUVOUUHUTZYEYRVAPUVRCNDZUVTNDZUWRUVLUXAYPUV
      PUUHUVLXPCUGDZUXAXPYDUVKVBZCUGUHVCZCVDVEOUVRUVOUVJUXBUVMUVNUVOUUHVGZUVLUV
      JYPUVPUUHUVGUVIUVJVHOZYSYGVAPCUVTVAPUVSUWAVIPUVRUWDNDZUWENDZUWGUVRUVIUVOU
      XHUWSUXFYEYSVAPUVRUVNUVJUXIUWTUXGYRYGVAPUWDUWEVIPUVRUWJUWOUVRXTYIUUAEFZUV
      SYTYHEFZHFZYEYTEFZYRYHEFZHFZHFZUWIUVRAYIBUUAEUVMYJUVPUUHUVLYJYOUSVJUVQUUB
      UUGUSQUVRYERDZYHRDZYRRDZYTRDZUXJUXPIUVLUXQYPUVPUUHUVIUXQUVGUVJYEVKVLOZUVR
      YFRDZYGRDZUXRUVRCRDZUYBUVLUYDYPUVPUUHUVLXPUXCUYDUXDUXECVMVEOZCVNURZUVLUYC
      YPUVPUUHUVJUYCUVGUVIYGVKVOOZYFYGSPZUVPUXSUVMUUHUVNUXSUVOYRVKVPVQZUVRUYBYS
      RDZUXTUYFUVPUYJUVMUUHUVOUYJUVNYSVKVRVQZYFYSSPZYEYHYRYTVSWHZUVRUXLUWBUXOUW
      HHUVRUXKUWAUVSHUVRUXKYFYFEFZUVTEFZUWAUVRUYBUYJUYBUYCUXKUYOIUYFUYKUYFUYGYF
      YSYFYGVTWHUVRUYNCUVTEUVRYFJKFZUYNCUVRUYBUYPUYNIUYFYFWAURUVRUYDUYPCIUYECWB
      URZWCWDWETZUVRUXOYFUWDEFZYFUWEEFZHFZUWHUVRUXMUYSUXNUYTHUVRUXQUYBUYJUXMUYS
      IUYAUYFUYKYEYFYSWFWGUVRUXSUYBUYCUXNUYTIUYIUYFUYGYRYFYGWFWGQUVRUWHVUAUVRUY
      BUWDRDZUWERDZUWHVUAIUYFUVRUXQUYJVUBUYAUYKYEYSSPZUVRUXSUYCVUCUYIUYGYRYGSPZ
      YFUWDUWEWIWGWJWEZQZWKUVRUWNUXJYEYHLFZYRYTLFZEFZEFZYKUYPYLEFZLFZUUCUYPUUDE
      FZLFZEFZMUVRUWNUWKUWHJKFZLFZUWIUWBUWHLFZEFZVUKUVRUWMVUQUWKLUVRVUQUYPUWLEF
      ZUWMUVRUYBUWFRDZVUQVVAIUYFUVRVUBVUCVVBVUDVUEUWDUWEWLPZYFUWFWMPUVRUYPCUWLE
      UYQWDWNTUVRUWBRDZUWHRDZVURVUTIUVRUVSRDZUWARDZVVDUVRUXQUXSVVFUYAUYIYEYRSPU
      VRUYDUVTRDZVVGUYEUVRUYJUYCVVHUYKUYGYSYGSPCUVTSPUVSUWAWLPUVRUYBVVBVVEUYFVV
      CYFUWFSPUWBUWHWOPUVRUWIUXJVUSVUJEUVRUXJUXPUWIUYMVUGWNUVRVUJUXLUXOLFZVUSUV
      RUXQUXRUXSUXTVUJVVIIUYAUYHUYIUYLYEYHYRYTWPWHUVRUXLUWBUXOUWHLUYRVUFQWNQWKU
      VRVUKYIVUHEFZUUAVUIEFZEFZYKYHJKFZLFZUUCYTJKFZLFZEFZVUPUVRYIRDZUUARDZVUHRD
      ZVUIRDZVUKVVLIUVRUXQUXRVVRUYAUYHYEYHWLPUVRUXSUXTVVSUYIUYLYRYTWLPUVRUXQUXR
      VVTUYAUYHYEYHWQPUVRUXSUXTVWAUYIUYLYRYTWQPYIUUAVUHVUIVTWHUVRVVQVVLUVRVVNVV
      JVVPVVKEUVRUXQUXRVVNVVJIUYAUYHYEYHWOPUVRUXSUXTVVPVVKIUYIUYLYRYTWOPQWJUVRV
      VNVUMVVPVUOEUVRVVMVULYKLUVRUYBUYCVVMVULIUYFUYGYFYGWMPTUVRVVOVUNUUCLUVRUYB
      UYJVVOVUNIUYFUYKYFYSWMPTQWKUVRVUPYNUUFEFMMEFZMUVRVUMYNVUOUUFEUVRVULYMYKLU
      VRUYPCYLEUYQWDTUVRVUNUUEUUCLUVRUYPCUUDEUYQWDTQUVRYNMUUFMEUVMYOUVPUUHUVLYJ
      YOVHVJUVQUUBUUGVHQVWBMIUVRMWRWSWTWKWKXAUVCUWPXTUWBUUOHFZIZUWKUUTLFZMIZGUE
      UFUWBUWFNNUUMUWBIZUUQVWDUVBVWFVWGUUPVWCXTUUMUWBUUOHXBXCVWGUVAVWEMVWGUURUW
      KUUTLUUMUWBJKXBWDXDXEUUNUWFIZVWDUWJVWFUWOVWHVWCUWIXTVWHUUOUWHUWBHUUNUWFYF
      EXFTXCVWHVWEUWNMVWHUUTUWMUWKLVWHUUSUWLCEUUNUWFJKXBTTXDXEXIWGXAXJXGXJXGXKX
      JXKXPUVFYBYQGZYCUUIGZGUUKXPXRVWIXSVWJUAUBACXHUCUDBCXHXEYBYQYCUUIXLXMUEUFX
      TCXHXNXO $.
      $( [18-Sep-2014] $)

    $( [ Characterize the right branch Pell14 as the positive elements ] $)

    $( A positive Pell solution is a general Pell solution.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrss1234 $p |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) C_ (
        Pell1234QR ` D ) ) $=
      ( va vb vc cn csquarenn cdif wcel cpell14qr cv cmul co wceq c2 cexp wa cz
      cfv wrex cn0 cpell1234qr cr csqr caddc cmin c1 a1i anim1d reximdv2 anim2d
      wi nn0z elpell14qr elpell1234qr 3imtr4d ssrdv ) AEFGHZBAIRZAUARZUQBJZUBHZ
      UTCJZAUCRDJZKLUDLMVBNOLAVCNOLKLUELUFMPDQSZCTSZPVAVDCQSZPUTURHUTUSHUQVEVFV
      AUQVDVDCTQUQVBTHZVBQHZVDVGVHUKUQVBULUGUHUIUJCDUTAUMCDUTAUNUOUP $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a real number.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR ) $=
      ( cn csquarenn cdif cpell14qr cfv cpell1234qr pell14qrss1234 pell1234qrre
      wcel cr sselda syldan ) BCDEKZABFGZKABHGZKALKOPQABIMABJN $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a nonzero number.  (Contributed by Stefan
       O'Rear, 17-Sep-2014.) $)
    pell14qrne0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A
        =/= 0 ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpell1234qr cc0 wne pell14qrss1234
      sselda pell1234qrne0 syldan ) BCDEFZABGHZFABIHZFAJKPQRABLMABNO $.
      $( [17-Sep-2014] $)

    $( A positive Pell solution is a positive number.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrgt0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> 0 <
        A ) $=
      ( va vb wcel cfv cc0 clt wbr cr cmul co wceq c2 cexp syl syl2anc ad2antlr
      wa cc cn csquarenn cdif cpell14qr cv csqr caddc cmin c1 cz cn0 elpell14qr
      wrex cabs 0cn a1i cle eldifi ad3antrrr nnre nnnn0 nn0ge0 3syl resqrcl zre
      adantl remulcl recnd abssub subid1 fveq2d eqtrd absresq sqrcl sqmul sqrth
      oveq1d 3eqtrd simpr breqtrrd wb resqcl nn0re adantr posdif mpbird eqbrtrd
      lt01 abscl absge0 lt2sq syl22anc 0re absdiflt syl3anc mpbid simprd addcom
      nn0cn adantrl simprl ex rexlimdvva expimpd sylbid imp ) BUAUBUCEZABUDFEZG
      AHIZXGXHAJEZACUEZBUFFZDUEZKLZUGLZMZXKNOLZBXMNOLZKLZUHLZUIMZSZDUJUMCUKUMZS
      XICDABULXGXJYCXIXGXJSZYBXICDUKUJYDXKUKEZXMUJEZSZSZYBXIYHYBSGXOAHYHYAGXOHI
      XPYHYASZGXNXKUGLZXOHYIXNXKUHLGHIZGYJHIZYIGXNUHLUNFZXKHIZYKYLSZYIYMXNUNFZX
      KHYIYMXNGUHLZUNFZYPYIGTEZXNTEZYMYRMYSYIUOUPYIXNYIXLJEZXMJEZXNJEZYIBJEZGBU
      QIZUUAYIBUAEZUUDXGUUFXJYGYABUAUBURUSZBUTPZYIUUFBUKEUUEUUGBVABVBVCBVDQYGUU
      BYDYAYFUUBYEXMVEVFZRZXLXMVGQZVHZGXNVIQYIYQXNUNYIYTYQXNMUULXNVJPVKVLYIYPXK
      HIZYPNOLZXQHIZYIUUNXSXQHYIUUNXNNOLZXLNOLZXRKLZXSYIUUCUUNUUPMUUKXNVMPYIXLT
      EZXMTEZUUPUURMYIBTEZUUSYIBUUHVHZBVNPYGUUTYDYAYGXMUUIVHRXLXMVOQYIUUQBXRKYI
      UVAUUQBMUVBBVPPVQVRYIXSXQHIZGXTHIZYIGUIXTHGUIHIYIWHUPYHYAVSVTYIXSJEZXQJEZ
      UVCUVDWAYIUUDXRJEZUVEUUHYIUUBUVGUUJXMWBPBXRVGQYIXKJEZUVFYGUVHYDYAYEUVHYFX
      KWCWDRZXKWBPXSXQWEQWFWGYIYPJEZGYPUQIZUVHGXKUQIZUUMUUOWAYIYTUVJUULXNWIPYIY
      TUVKUULXNWJPUVIYGUVLYDYAYEUVLYFXKVBWDRYPXKWKWLWFWGYIGJEZUUCUVHYNYOWAUVMYI
      WMUPUUKUVIGXNXKWNWOWPWQYIXKTEZYTXOYJMYGUVNYDYAYEUVNYFXKWSWDRUULXKXNWRQVTW
      TYHXPYAXAVTXBXCXDXEXF $.
      $( [18-Sep-2014] $)

    $( A positive Pell solution is a positive real.  (Contributed by Stefan
       O'Rear, 19-Sep-2014.) $)
    pell14qrrp $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR+ ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cc0 clt wbr pell14qrre pell14qrgt0
      wa cr crp elrp sylanbrc ) BCDEFABGHFNAOFIAJKAPFABLABMAQR $.
      $( [19-Sep-2014] $)

    $( A general Pell solution is either a positive solution, or its negation
       is.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrdich $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) ->
        ( A e. ( Pell14QR ` D ) \/ -u A e. ( Pell14QR ` D ) ) ) $=
      ( va vb vc wcel cneg cmul co caddc wceq c2 cexp cmin c1 wa wrex ad3antrrr
      cz cn0 vd cn csquarenn cdif cpell1234qr cpell14qr wo cr csqr elpell1234qr
      cfv cv elznn0 simprbi adantl elpell14qr adantr simplr ad2antrr weq eqeq2d
      wi wb oveq1 oveq1d eqeq1d anbi12d rexbidv rcla4ev adantll mpbir2and exp31
      orcd renegcl syl simpllr znegcl ad2antlr simprl negeqd cc zcn eldifi nncn
      sqrcl mulcl syl2anc negdi mulneg2 eqcomd oveq2d 3eqtrd sqneg simprr eqtrd
      oveq12d oveq2 rcla42ev syl112anc olcd ex rexlimdva mpd expimpd sylbid imp
      jaod ) BUBUCUDFZABUEUKFZABUFUKZFZAGZXJFZUGZXHXIAUHFZACULZBUIUKZDULZHIZJIZ
      KZXPLMIZBXRLMIZHIZNIZOKZPZDSQZCSQZPXNCDABUJXHXOYIXNXHXOPZYHXNCSYJXPSFZPZX
      PTFZXPGZTFZUGZYHXNVBZYKYPYJYKXPUHFYPXPUMUNUOYLYMYQYOYLYMYHXNYLYMPYHPZXKXM
      YRXKXOAEULZXSJIZKZYSLMIZYDNIZOKZPZDSQZETQZYJXKXOUUGPVCZYKYMYHXHUUHXOEDABU
      PUQRYLXOYMYHXHXOYKURZUSYMYHUUGYLUUFYHEXPTECUTZUUEYGDSUUJUUAYAUUDYFUUJYTXT
      AYSXPXSJVDVAUUJUUCYEOUUJUUBYBYDNYSXPLMVDVEVFVGVHVIVJVKVMVLYLYOYQYLYOPZYGX
      NDSUUKXRSFZPZYGXNUUMYGPZXMXKUUNXMXLUHFZXLYSXQUAULZHIZJIZKZUUBBUUPLMIZHIZN
      IZOKZPZUASQETQZYLXMUUOUVEPVCZYOUULYGXHUVFXOYKEUAXLBUPUSRUUNXOUUOYLXOYOUUL
      YGUUIRAVNVOUUNYOXRGZSFZXLYNXQUVGHIZJIZKZYNLMIZBUVGLMIZHIZNIZOKZUVEYLYOUUL
      YGVPUULUVHUUKYGXRVQVRUUNXLXTGZYNXSGZJIZUVJUUNAXTUUMYAYFVSVTUUNXPWAFZXSWAF
      ZUVQUVSKYLUVTYOUULYGYKUVTYJXPWBUORZUUNXQWAFZXRWAFZUWAUUNBWAFZUWCYLUWEYOUU
      LYGXHUWEXOYKXHBUBFUWEBUBUCWCBWDVOUSRBWEVOZUULUWDUUKYGXRWBVRZXQXRWFWGXPXSW
      HWGUUNUVRUVIYNJUUNUWCUWDUVRUVIKUWFUWGUWCUWDPUVIUVRXQXRWIWJWGWKWLUUNUVOYEO
      UUNUVLYBUVNYDNUUNUVTUVLYBKUWBXPWMVOUUNUVMYCBHUUNUWDUVMYCKUWGXRWMVOWKWPUUM
      YAYFWNWOUVDUVKUVPPXLYNUUQJIZKZUVLUVANIZOKZPEUAYNUVGTSYSYNKZUUSUWIUVCUWKUW
      LUURUWHXLYSYNUUQJVDVAUWLUVBUWJOUWLUUBUVLUVANYSYNLMVDVEVFVGUUPUVGKZUWIUVKU
      WKUVPUWMUWHUVJXLUWMUUQUVIYNJUUPUVGXQHWQWKVAUWMUWJUVOOUWMUVAUVNUVLNUWMUUTU
      VMBHUUPUVGLMVDWKWKVFVGWRWSVKWTXAXBXAXGXCXBXDXEXF $.
      $( [18-Sep-2014] $)

    $( A number is a positive Pell solution iff it is positive and a Pell
       solution, justifying our name choice.  (Contributed by Stefan O'Rear,
       19-Oct-2014.) $)
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

    $( Positive Pell solutions are closed under multiplication.  (Contributed
       by Stefan O'Rear, 17-Sep-2014.) $)
    pell14qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ( Pell14QR ` D ) ) -> ( A x. B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cmul co cpell1234qr cc0 clt wbr wa
      cr pell1234qrre syldan elpell14qr2 simprll simprrl pell1234qrmulcl mulgt0
      simpl syl3anc simprlr simprrr syl22anc jca ex anbi12d 3imtr4d 3impib ) CD
      EFGZACHIZGZBUPGZABJKZUPGZUOACLIZGZMANOZPZBVAGZMBNOZPZPZUSVAGZMUSNOZPZUQUR
      PUTUOVHVKUOVHPZVIVJVLUOVBVEVIUOVHUEUOVBVCVGUAZUOVDVEVFUBZABCUCUFVLAQGZVCB
      QGZVFVJUOVHVBVOVMACRSUOVBVCVGUGUOVHVEVPVNBCRSUOVDVEVFUHABUDUIUJUKUOUQVDUR
      VGACTBCTULUSCTUMUN $.
      $( [17-Sep-2014] $)

    $( Positive Pell solutions are closed under reciprocal.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> (
        1 / A ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv c1 cdiv co cpell1234qr cc0 clt wbr
      wa pell1234qrreccl adantrr cr elpell14qr2 pell1234qrre simprr syl2anc jca
      recgt0 ex 3imtr4d imp ) BCDEFZABGHZFZIAJKZUJFZUIABLHZFZMANOZPZULUNFZMULNO
      ZPZUKUMUIUQUTUIUQPZURUSUIUOURUPABQRVAASFZUPUSUIUOVBUPABUARUIUOUPUBAUEUCUD
      UFABTULBTUGUH $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are closed under division.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
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

    $( Positive Pell solutions are closed under integer powers.  (Contributed
       by Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrexpcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ZZ ) -> ( A ^ B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv co cn0 wa simplll pell14qrexpclnn0
      cexp simpllr simpr syl3anc cc recnd cz cr cneg wo c1 cdiv wceq pell14qrre
      elznn0 ad2antrr simplr expneg2 pell14qrreccl syl2anc jaodan syl5bi 3impia
      eqeltrd expl ) CDEFGZACHIZGZBUAGZABOJZVAGZVCBUBGZBKGZBUCZKGZUDZLUTVBLZVEB
      UIVKVFVJVEVKVFLZVGVEVIVLVGLUTVBVGVEUTVBVFVGMUTVBVFVGPVLVGQABCNRVLVILZVDUE
      AVHOJZUFJZVAVMASGZBSGVIVDVOUGVKVPVFVIVKAACUHTUJVMBVKVFVIUKTVLVIQZABULRVMU
      TVNVAGZVOVAGUTVBVFVIMZVMUTVBVIVRVSUTVBVFVIPVQAVHCNRVNCUMUNURUOUSUPUQ $.
      $( [18-Sep-2014] $)

    $( First-quadrant Pell solutions are a subset of the positive solutions.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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
       reciprocal is.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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

    $( A Pell solution in the first quadrant is at least 1.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
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

    $( 1 is a Pell solution and in the first quadrant as one.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
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
       which are at least one.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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
      wo sylib nnge1 simplrl oveq1 sq0 eqtrd oveq2d mul01 recnd sqcl subid1 sq1
      eqcomi 3eqtr3d nn0ge0 1re 1nn0 nn0ge0i sq11 syl22anc simpr oveq12d ax-1cn
      addid1i breqtrd ltnri pm2.24 jaodan mpdan rpgt0 lemul2 syl112anc eqbrtrrd
      wn sylc leadd2 syl3anc le2sq resqcl suble0 mpbird resubcl 0re nngt0 sqrth
      simprr eqcomd mulcl subdi oveq1d eqtr2d 3eqtrd addid1 3brtr4d rpge0 letrd
      addsub12 leadd1 ) CUADZAUBDZBUBDZUCZUCZEACUDUEZBFGZHGZUFIZAUOUGGZCBUOUGGZ
      FGZJGZEKZUCZUCZCEHGZUDUEZYJHGZUUBYKHGZYLYTUUBLDZYJLDZUUCLDYTUUBUHDZUUEYTU
      UAUHDZUUGYTCUHDZEUHDZUUHYEUUIYHYSCUIUJZUUJYTUKMCEULNZUUAUMOZUUBUNOZYTYJUH
      DZUUFYTUUIUUOUUKCUMOZYJUNOZUUBYJUPNYTUUEYKLDZUUDLDUUNYTUUFBLDZUURUUQYHUUS
      YEYSYGUUSYFBUQURUSZYJBUTNZUUBYKUPNYTALDZUURYLLDYHUVBYEYSYFUVBYGAUQVAUSZUV
      AAYKUPNYTYJYKPIZUUCUUDPIZYTYJEFGZYJYKPYTYJQDZUVFYJKYTUUOUVGUUPYJVBOZYJVCO
      YTEBPIZUVFYKPIZYTBUADZBRKZVFZUVIYTYGUVMYEYFYGYSVDBVEVGYTUVKUVIUVLUVKUVIYT
      BVHURYTUVLUCZEEUFIZUVOWTZUVIUVNEYLEUFYIYMYRUVLVIUVNYLERHGZEUVNAEYKRHUVNYN
      EUOUGGZKZAEKZUVNYQEYNUVRYIYMYRUVLVDUVNYQYNRJGZYNUVNYPRYNJUVNYPCRFGZRUVNYO
      RCFUVNYORUOUGGZRUVLYOUWCKYTBRUOUGVJURUWCRKUVNVKMVLVMUVNCQDZUWBRKZYTUWDUVL
      YTUUIUWDUUKCVBOZVACVNZOVLVMUVNYNQDZUWAYNKYTUWHUVLYTAQDUWHYTAUVCVOAVPOZVAY
      NVQOVLEUVRKUVNUVREVRVSMVTYTUVSUVTTZUVLYTUVBRAPIZELDZREPIZUWJUVCYHUWKYEYSY
      FUWKYGAWAVAUSZUWLYTWBMZUWMYTEWCWDMZAEWEWFVASUVNYKYJRFGZRUVNBRYJFYTUVLWGVM
      UVNUVGUWQRKYTUVGUVLUVHVAYJVNOVLWHUVQEKUVNEWIWJMVLWKUVPUVNEWBWLMUVOUVIWMXA
      WNWOZYTUWLUUSUUFRYJUFIZUVIUVJTUWOUUTUUQYTUUOUWSUUPYJWPOEBYJWQWRSWSYTUUFUU
      RUUEUVDUVETUUQUVAUUNYJYKUUBXBXCSYTUUBAPIZUUDYLPIZYTUWTUUBUOUGGZYNPIZYTYNC
      EYOJGZFGZHGZYNUWBHGZUXBYNPYTUXEUWBPIZUXFUXGPIZYTUXDRPIZUXHYTUXJEYOPIZYTUV
      REYOPUVREKYTVRMYTUVIUVRYOPIZUWRYTUWLUWMUUSRBPIZUVIUXLTUWOUWPUUTYHUXMYEYSY
      GUXMYFBWAURUSEBXDWFSWSYTUWLYOLDZUXJUXKTUWOYTUUSUXNUUTBXEOZEYOXFNXGYTUXDLD
      ZRLDZCLDZRCUFIZUXJUXHTYTUWLUXNUXPUWOUXOEYOXHNZUXQYTXIMZYTUUIUXRUUKCUNOZYE
      UXSYHYSCXJUJUXDRCWQWRSYTUXELDZUWBLDZYNLDZUXHUXITYTUXRUXPUYCUYBUXTCUXDUTNY
      TUXRUXQUYDUYBUYACRUTNYTUVBUYEUVCAXEOUXEUWBYNXBXCSYTUXBUUACYQHGZUXFYTUUAQD
      ZUXBUUAKYTUUHUYGUULUUAVBOUUAXKOYTEYQCHYTYQEYIYMYRXLXMVMYTUYFYNCYPJGZHGZUX
      FYTUWDUWHYPQDZUYFUYIKUWFUWIYTUWDYOQDZUYJUWFYTBQDUYKYTBUUTVOBVPOZCYOXNNCYN
      YPYCXCYTUYHUXEYNHYTUXECEFGZYPJGZUYHYTUWDEQDUYKUXEUYNKUWFYTEUWOVOUYLCEYOXO
      XCYTUYMCYPJYTUWDUYMCKUWFCVCOXPXQVMVLXRYTUXGYNRHGZYNYTUWBRYNHYTUWDUWEUWFUW
      GOVMYTUWHUYOYNKUWIYNXSOXQXTYTUUERUUBPIZUVBUWKUWTUXCTUUNYTUUGUYPUUMUUBYAOU
      VCUWNUUBAXDWFXGYTUUEUVBUURUWTUXATUUNUVCUVAUUBAYKYDXCSYB $.
      $( [18-Sep-2014] $)

    $( First-quadrant Pell solutions are bounded away from 1.  (This particular
       bound allows us to prove exact values for the fundamental solution
       later.)  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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

    $( Positive Pell solutions are bounded away from 1.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrgap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> ( ( sqr ` ( D + 1 ) ) + ( sqr ` D ) ) <_ A ) $=
      ( cn csquarenn cdif wcel cpell1qr cfv cpell14qr c1 clt wbr caddc csqr cle
      co w3a wa wb cr elpell1qr2 3ad2ant1 wi 1re pell14qrre ltle sylancr 3impia
      simp2 mpbir2and pell1qrgap syld3an2 ) BCDEFZABGHFZABIHFZJAKLZBJMPNHBNHMPA
      OLUMUOUPQUNUOJAOLZUMUOUNUOUQRSUPABUAUBUMUOUPUIUMUOUPUQUMUORJTFATFUPUQUCUD
      ABUEJAUFUGUHUJABUKUL $.
      $( [18-Sep-2014] $)

    $( Positive Pell solutions are bounded away from 1, with a friendlier
       bound.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrgapw $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> 2 < A ) $=
      ( cn wcel cfv c1 clt wbr c2 caddc co cr a1i crp syl 1re cexp cle wceq wb
      csquarenn cdif cpell14qr w3a csqr 2re eldifi 3ad2ant1 1rp rpaddcl syl2anc
      nnrp rpsqrcl rpre readdcl pell14qrre 3adant3 df-2 readdcli peano2re nnge1
      nnre ltp1 lelttrd sq1 cc nncn peano2cn sqrth 3brtr4d cc0 1nn0 rpge0 lt2sq
      nn0ge0i syl22anc mpbird ltadd1 syl3anc mpbid ltletrd syl5eqbr pell14qrgap
      le2sq leadd2 ) BCUAUBDZABUCEDZFAGHZUDZIBFJKZUEEZBUEEZJKZAILDWIUFMWIWKLDZW
      LLDZWMLDWIWKNDZWNWIWJNDZWPWIBNDZFNDZWQWIBCDZWRWFWGWTWHBCUAUGUHZBULOZWSWIU
      IMBFUJUKWJUMOZWKUNOZWIWLNDZWOWIWRXEXBBUMOZWLUNOZWKWLUOUKZWFWGALDWHABUPUQW
      IIFFJKZWMGURWIXIWKFJKZWMXILDWIFFPPUSMWIWNXJLDXDWKUTOXHWIFWKGHZXIXJGHZWIXK
      FIQKZWKIQKZGHZWIFWJXMXNGWIFBWJFLDZWIPMZWIWTBLDZXABVBOZWIXRWJLDXSBUTOWIWTF
      BRHXABVAOZWIXRBWJGHXSBVCOVDXMFSWIVEMZWIWJVFDZXNWJSWIBVFDZYBWIWTYCXABVGOZB
      VHOWJVIOVJWIXPVKFRHZWNVKWKRHZXKXOTXQYEWIFVLVOMZXDWIWPYFXCWKVMOFWKVNVPVQWI
      XPWNXPXKXLTXQXDXQFWKFVRVSVTWIFWLRHZXJWMRHZWIYHXMWLIQKZRHZWIFBXMYJRXTYAWIY
      CYJBSYDBVIOVJWIXPYEWOVKWLRHZYHYKTXQYGXGWIXEYLXFWLVMOFWLWDVPVQWIXPWOWNYHYI
      TXQXGXDFWLWKWEVSVTWAWBABWCWA $.
      $( [18-Sep-2014] $)

    $( Condition for a calculated real to be a Pell solution.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
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
       to its infimum, one-direction version.  (Contributed by Stefan O'Rear,
       1-Sep-2013.) $)
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
         quadrant.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
      pellqrex $p |- ( D e. ( NN \ []NN ) -> E. x e. ( Pell1QR ` D ) 1 < x ) $=
        ( vc vd cn csquarenn wcel cv c2 cexp co c1 wceq clt wbr wa 1re a1i cle
        cr va cdif cmul cmin wrex cpell1qr cfv cq wn eldifi eldifn anim1i fveq2
        csqr eleq1d df-squarenn elrab2 sylibr mtand pellex syl2anc caddc simpll
        cn0 nnnn0 adantr ad2antlr adantl simpr pellqrexplicit syl31anc readdcli
        nnre ad2antrl crp nnrp rpsqrcl rpre 3syl ad2antll remulcl readdcl ltp1i
        syl nnge1 ax-1cn mulid2i sq1 cc nncn sqrth 3brtr4d cc0 wb nn0ge0i rpge0
        le2sq syl22anc mpbird wi jctir lemul12a mp2and syl5eqbrr le2add ltletrd
        1nn0 breq2 rcla4ev ex rexlimdvva mpd ) BEFUBGZCHZIJKBDHZIJKUCKUDKLMZDEU
        ECEUEZLAHZNOZABUFUGZUEZXMBEGZBUNUGZUHGZUIXQBEFUJZXMYDBFGZBEFUKXMYDPYBYD
        PYFXMYBYDYEULUAHZUNUGZUHGYDUABEFYGBMYHYCUHYGBUNUMUOUAUPUQURUSCDBUTVAXMX
        PYACDEEXMXNEGZXOEGZPZPZXPYAYLXPPZXNYCXOUCKZVBKZXTGZLYONOZYAYMXMXNVDGZXO
        VDGZXPYPXMYKXPVCYKYRXMXPYIYRYJXNVEVFVGYKYSXMXPYJYSYIXOVEVHVGYLXPVIXNXOB
        VJVKYLYQXPYLLLLVBKZYOLTGZYLQRZYTTGYLLLQQVLRYLXNTGZYNTGZYOTGYIUUCXMYJXNV
        MVNZYLYCTGZXOTGZUUDYLBVOGZYCVOGZUUFYLYBUUHXMYBYKYEVFZBVPZWDBVQZYCVRZVSZ
        YJUUGXMYIXOVMVTZYCXOWAVAZXNYNWBVALYTNOYLLQWCRYLLXNSOZLYNSOZYTYOSOZYIUUQ
        XMYJXNWEVNYLLLLUCKZYNSLWFWGYLLYCSOZLXOSOZUUTYNSOZYLYBUVAUUJYBUVALIJKZYC
        IJKZSOZYBLBUVDUVESBWEUVDLMYBWHRYBBWIGUVEBMBWJBWKWDWLYBUUAWMLSOZUUFWMYCS
        OZUVAUVFWNUUAYBQRUVGYBLXGWOZRYBUUHUUIUUFUUKUULUUMVSYBUUHUUIUVHUUKUULYCW
        PVSLYCWQWRWSWDYJUVBXMYIXOWEVTYLUUAUVGPZUUFUVJUUGUVAUVBPUVCWTYLUUAUVGUUB
        UVIXAZUUNUVKUUOLYCLXOXBWRXCXDYLUUAUUAUUCUUDUUQUURPUUSWTUUBUUBUUEUUPLLXN
        YNXEWRXCXFVFXSYQAYOXTXRYOLNXHXIVAXJXKXL $.
        $( [18-Sep-2014] $)
    $}

    ${
      $d D x $.
      $( Value of the fundamental solution of a Pell equation.  (Contributed by
         Stefan O'Rear, 18-Sep-2014.) $)
      pellfundval $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) = sup ( { x e.
          ( Pell14QR ` D ) | 1 < x } , RR , `' < ) ) $=
        ( va c1 cv clt wbr cpell14qr crab cr ccnv csup csquarenn cdif cpellfund
        cfv cn wceq fveq2 wor rabeq syl df-pellfund ltso cnvso mpbi supex fvmpt
        supeq1d ) CBDAEFGZACEZHPZIZJFKZLUJABHPZIZJUNLQMNOUKBRZJUMUPUNUQULUORUMU
        PRUKBHSUJAULUOUAUBUICAUCJUPUNJFTJUNTUDJFUEUFUGUH $.
        $( [18-Sep-2014] $)
    $}

    $( The fundamental solution of a Pell equation exists as a real number.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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

    $( Lower bound on the fundamental solution of a Pell equation.
       (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
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

    $( Weak lower bound on the Pell fundamental solution.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
    pellfundgt1 $p |- ( D e. ( NN \ []NN ) -> 1 < ( PellFund ` D ) ) $=
      ( cn csquarenn wcel c1 caddc co csqr cfv cr a1i crp syl nnrp 3syl wbr cle
      sqr1 cc0 wa cdif cpellfund 1re eldifi peano2nn rpsqrcl readdcl pellfundre
      rpre syl2anc syl5eqel c2 1lt2 oveq12i 1p1e2apr1 eqtri breqtrri nnge1 nnre
      clt wb peano2re 1nn0 nn0ge0i cn0 nnnn0 nn0ge0 sqrle syl22anc mpbid le2add
      3impia syl222anc ltletrd pellfundge ) ABCUADZEAEFGZHIZAHIZFGZAUBIEJDZVPUC
      KZVPVRJDZVSJDZVTJDVPVQLDZVRLDWCVPVQBDZWEVPABDZWFABCUDZAUEMZVQNMVQUFVRUIOZ
      VPALDZVSLDWDVPWGWKWHANMAUFVSUIOZVRVSUGUJZAUHVPEEHIZWNFGZVTWBVPWNJDZWPWOJD
      VPWNEJRWBUKZWQWNWNUGUJWMEWOUTPVPEULWOUTUMWOEEFGULWNEWNEFRRUNUOUPUQKVPWPWP
      WCWDWNVRQPZWNVSQPZWOVTQPZWQWQWJWLVPEVQQPZWRVPWFXAWIVQURMVPWAVQJDZSEQPZSVQ
      QPZXAWRVAWBVPAJDZXBVPWGXEWHAUSMZAVBMXCVPEVCVDKZVPWFVQVEDXDWIVQVFVQVGOEVQV
      HVIVJVPEAQPZWSVPWGXHWHAURMVPWAXEXCSAQPZXHWSVAWBXFXGVPWGAVEDXIWHAVFAVGOEAV
      HVIVJWPWPTWCWDTWRWSTWTWNWNVRVSVKVLVMVNAVOVN $.
      $( [19-Sep-2014] $)

    $( A nontrivial first quadrant solution is at least as large as the
       fundamental solution.  (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
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
         nontrivial solution less than it.  (Contributed by Stefan O'Rear,
         18-Sep-2014.) $)
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

    $( The fundamental solution as an infimum is itself a solution, showing
       that the solution set is discrete.

       Since the fundamental solution is an infimum, there must be an element
       ge to Fund and lt 2*Fund.  If this element is equal to the fundamental
       solution we're done, otherwise use the infimum again to find another
       element which must be ge Fund and lt the first element; their ratio is a
       group element in (1,2), contradicting ~ pell14qrgapw .  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
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

    $( There are no solutions between 1 and the fundamental solution.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
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

    $( The fundamental Pell solution is a positive real.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
    pellfundrp $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR+ ) $=
      ( cn csquarenn cdif wcel cpellfund cfv cc0 clt wbr crp pellfundre 0re a1i
      cr c1 1re lt01 pellfundgt1 lttrd elrp sylanbrc ) ABCDEZAFGZOEHUDIJUDKEALZ
      UCHPUDHOEUCMNPOEUCQNUEHPIJUCRNASTUDUAUB $.
      $( [19-Sep-2014] $)

    $( The fundamental Pell solution is never 1.  (Contributed by Stefan
       O'Rear, 19-Sep-2014.) $)
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
       natural logarithms.  (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
    logne0 $p |- ( ( A e. RR+ /\ A =/= 1 ) -> ( log ` A ) =/= 0 ) $=
      ( crp wcel c1 wne wa clog cfv cc0 ce simpr wceq ef0 neeqtrrd necomd cr wb
      a1i 0re relogeftb syldan necon3bid mpbird ) ABCZADEZFZAGHZIEIJHZAEUFAUHUF
      ADUHUDUEKUHDLUFMRNOUFUGIUHAUDUEIPCZUGILUHALQUIUFSRAITUAUBUC $.
      $( [19-Sep-2014] $)

    $( General logarithm is a real number.  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    reglogcl $p |- ( ( A e. RR+ /\ B e. RR+ /\ B =/= 1 ) -> ( ( log ` A ) / (
        log ` B ) ) e. RR ) $=
      ( crp wcel c1 wne w3a clog cfv cr cc0 co relogcl 3ad2ant1 3ad2ant2 logne0
      cdiv 3adant1 redivcl syl3anc ) ACDZBCDZBEFZGAHIZJDZBHIZJDZUFKFZUDUFQLJDUA
      UBUEUCAMNUBUAUGUCBMOUBUCUHUABPRUDUFST $.
      $( [19-Sep-2014] $)

    $( General logarithm preserves "less than".  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    reglogltb $p |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) ->
        ( A < B <-> ( ( log ` A ) / ( log ` C ) ) < ( ( log ` B ) / ( log ` C )
        ) ) ) $=
      ( crp wcel wa c1 clt wbr clog cfv cdiv co wb logltb adantr cr cc0 relogcl
      ad2antrr ad2antlr ad2antrl log1 mpan biimpa syl5eqbrr adantl ltdiv1 bitrd
      1rp syl112anc ) ADEZBDEZFZCDEZGCHIZFZFZABHIZAJKZBJKZHIZUTCJKZLMVAVCLMHIZU
      NUSVBNUQABOPURUTQEZVAQEZVCQEZRVCHIZVBVDNULVEUMUQASTUMVFULUQBSUAUOVGUNUPCS
      UBUQVHUNUQRGJKZVCHUCUOUPVIVCHIZGDEUOUPVJNUJGCOUDUEUFUGUTVAVCUHUKUI $.
      $( [19-Sep-2014] $)

    $( Natural logarithm preserves ` <_ ` .  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    logleb $p |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A <_ B <-> ( log ` A ) <_ (
        log ` B ) ) ) $=
      ( crp wcel wa clt wbr wn clog cfv cle wb logltb ancoms notbid rpre syl2an
      cr lenlt relogcl 3bitr4d ) ACDZBCDZEZBAFGZHZBIJZAIJZFGZHZABKGZUHUGKGZUDUE
      UIUCUBUEUILBAMNOUBARDBRDUKUFLUCAPBPABSQUBUHRDUGRDULUJLUCATBTUHUGSQUA $.
      $( [19-Sep-2014] $)

    $( General logarithm preserves ` <_ ` .  (Contributed by Stefan O'Rear,
       19-Oct-2014.) $)
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

    $( Multiplication law for general log.  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
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

    $( Power law for general log.  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    reglogexp $p |- ( ( A e. RR+ /\ N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( (
        log ` ( A ^ N ) ) / ( log ` C ) ) = ( N x. ( ( log ` A ) / ( log ` C )
        ) ) ) $=
      ( crp wcel cz c1 wne wa w3a co clog cdiv cmul wceq relogcl recnd 3ad2ant3
      cfv cc cexp relogexp 3adant3 oveq1d cc0 zcn 3ad2ant2 adantr logne0 divass
      3ad2ant1 syl112anc eqtrd ) ADEZCFEZBDEZBGHZIZJZACUAKLSZBLSZMKCALSZNKZVAMK
      ZCVBVAMKNKZUSUTVCVAMUNUOUTVCOURACUBUCUDUSCTEZVBTEZVATEZVAUEHZVDVEOUOUNVFU
      RCUFUGUNUOVGURUNVBAPQUKURUNVHUOUPVHUQUPVABPQUHRURUNVIUOBUIRCVBVAUJULUM $.
      $( [19-Sep-2014] $)

    $( General log of the base is 1.  (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    reglogbas $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` C ) / ( log ` C ) )
        = 1 ) $=
      ( crp wcel c1 wne wa clog cfv cc cdiv co wceq relogcl recnd adantr logne0
      cc0 divid syl2anc ) ABCZADEZFAGHZICZUBQEUBUBJKDLTUCUATUBAMNOAPUBRS $.
      $( [19-Sep-2014] $)

    $( General log of 1 is 0.  (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
    reglog1 $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` 1 ) / ( log ` C ) ) =
        0 ) $=
      ( crp wcel c1 wne wa clog cfv cdiv co cc0 log1 oveq1i wceq relogcl adantr
      cc recnd logne0 div0 syl2anc syl5eq ) ABCZADEZFZDGHZAGHZIJKUGIJZKUFKUGILM
      UEUGQCZUGKEUHKNUCUIUDUCUGAORPASUGTUAUB $.
      $( [19-Sep-2014] $)

    $( General log of a power of the base is the exponent.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
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
      $( Every positive Pell solution is a power of the fundamental solution.
         (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
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
         not be using), throw in a copy of Z/2Z. (Contributed by Stefan O'Rear,
         19-Sep-2014.) $)
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
    $( Value of the X sequence.  Not used after ~ rmxyval is proved.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
    rmxfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) = ( 1st ` (
        `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqr caddc c1st cmul cmpt ccnv wceq
      cuz cn0 cxp c2nd wa oveq1 oveq1d fveq2d oveq2d mpteq2dv cnveqd adantr id1
      crmx oveq12d oveqan12d fveq12d df-rmx fvex ovmpt2a ) DEABFUAGHDIZVAFJKZLM
      KZNGZOKZEIZJKZCUBHUCZCIZPGZVDVIUDGZQKZOKZRZSZGZPGAAFJKZLMKZNGZOKZBJKZCVHV
      JVSVKQKZOKZRZSZGZPGUNVAATZVFBTZUEZVPWFPWIVGWAVOWEWGVOWETWHWGVNWDWGCVHVMWC
      WGVLWBVJOWGVDVSVKQWGVCVRNWGVBVQLMVAAFJUFUGUHZUGUIUJUKULWGWHVEVTVFBJWGVAAV
      DVSOWGUMWJUOWHUMUPUQUHEDCURWFPUSUT $.
      $( [21-Sep-2014] $)

    $( Value of the Y sequence.  Not used after ~ rmxyval is proved.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
    rmyfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY N ) = ( 2nd ` (
        `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqr caddc c2nd cmul cmpt ccnv wceq
      cuz cn0 cxp c1st wa oveq1 oveq1d fveq2d oveq2d mpteq2dv cnveqd adantr id1
      crmy oveq12d id oveqan12d fveq12d df-rmy fvex ovmpt2a ) DEABFUAGHDIZVBFJK
      ZLMKZNGZOKZEIZJKZCUBHUCZCIZUDGZVEVJPGZQKZOKZRZSZGZPGAAFJKZLMKZNGZOKZBJKZC
      VIVKVTVLQKZOKZRZSZGZPGUNVBATZVGBTZUEZVQWGPWJVHWBVPWFWHVPWFTWIWHVOWEWHCVIV
      NWDWHVMWCVKOWHVEVTVLQWHVDVSNWHVCVRLMVBAFJUFUGUHZUGUIUJUKULWHWIVFWAVGBJWHV
      BAVEVTOWHUMWKUOWIUPUQURUHEDCUSWGPUTVA $.
      $( [21-Sep-2014] $)
  $}

  $( The discriminant used to define the X and Y sequences has an irrational
     square root.  (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
  rmspecsqrnq $p |- ( A e. ( ZZ>= ` 2 ) -> ( sqr ` ( ( A ^ 2 ) - 1 ) ) e. ( CC
      \ QQ ) ) $=
    ( c2 wcel cexp co c1 cmin cc cq 3syl ax-1cn sylancl syl clt caddc cmul wceq
    wbr cr a1i cuz cfv csqr wn cdif cz eluzelz zcn sqcl subcl sqrcl cn0 eluz2b2
    cn wa biimpi simpld nnsqcl nnm1nn0 eluzelre recnd binom2sub 2re 1re remulcl
    sylancr resqcli recni subsub syl3anc eqtr4d 2timesi simprd cc0 wb syl112anc
    2pos ltmul2 mpbid syl5eqbrr ltaddsub mulid1 oveq2d oveq12d breqtrrd resubcl
    sq1 nnre ltsub2 eqbrtrd ltm1 npcan oveq1d nonsq syl22anc eldif sylanbrc ) A
    BUAUBCZABDEZFGEZUCUBZHCZXAICUDZXAHIUECWRWTHCZXBWRWSHCZFHCZXDWRAUFCAHCZXEBAU
    GAUHAUIJZKWSFUJLWTUKMWRWTULCZAFGEZULCZXJBDEZWTNRWTXJFOEZBDEZNRXCWRAUNCZWSUN
    CZXIWRXOFANRZWRXOXQUOAUMUPZUQZAURZWSUSJWRXOXKXSAUSMWRXLWSBAFPEZPEZFBDEZGEZG
    EZWTNWRXLWSYBGEYCOEZYEWRXGXFXLYFQWRABAUTZVAZKAFVBLWRXEYBHCYCHCZYEYFQXHWRYBW
    RBSCZYASCZYBSCZVCWRASCZFSCZYKYGVDAFVELBYAVEVFZVAYIWRYCFVDVGZVHTWSYBYCVIVJVK
    WRFYDNRZYEWTNRZWRFBAPEZFGEZYDNWRFFOEZYSNRZFYTNRZWRUUABFPEZYSNFKVLWRXQUUDYSN
    RZWRXOXQXRVMWRYNYMYJVNBNRZXQUUEVOYNWRVDTZYGYJWRVCTUUFWRVQTFABVRVPVSVTWRYNYN
    YSSCZUUBUUCVOUUGUUGWRYJYMUUHVCYGBAVEVFFFYSWAVJVSWRYBYSYCFGWRYAABPWRXGYAAQYH
    AWBMWCYCFQWRWGTWDWEWRYNYDSCZWSSCZYQYRVOUUGWRYLYCSCUUIYOYPYBYCWFLWRXOXPUUJXS
    XTWSWHJZFYDWSWIVJVSWJWRWTWSXNNWRUUJWTWSNRUUKWSWKMWRXMABDWRXGXFXMAQYHKAFWLLW
    MWEWTXJWNWOXAHIWPWQ $.
    $( [21-Sep-2014] $)

  ${
    $d a A $.
    $( The discriminant used to define the X and Y sequences is a nonsquare
       positive integer and thus a valid Pell equation discriminant.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
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
     sequences.  (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
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
     fundamental solution of the corresponding Pell equation.  (Contributed by
     Stefan O'Rear, 21-Sep-2014.) $)
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
       irrationals.  (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
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
       irrationals to pairs of integers.  (Contributed by Stefan O'Rear,
       21-Sep-2014.) $)
    rmxypairf1o $p |- ( A e. ( ZZ>= ` 2 ) -> ( b e. ( NN0 X. ZZ ) |-> ( ( 1st `
        b ) + ( ( sqr ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) : ( NN0 X. ZZ
        ) -1-1-onto-> { a | E. c e. NN0 E. d e. ZZ a = ( c + ( ( sqr ` ( ( A ^
        2 ) - 1 ) ) x. d ) ) } ) $=
      ( cfv wcel cn0 cz cv c1st co c2nd cmul caddc wceq wrex fveq2 cq 3syl cexp
      c2 cuz cxp c1 cmin csqr cmpt wfn crn cab weq wi wral wf1o eqid fnmpt ovex
      cvv a1i mprg wb cop op1st syl6eq op2nd oveq2d oveq12d eqeq2d rexxp bicomi
      abbidv rnmpt syl6reqr wa fvmpt ad2antrl ad2antll eqeq12d cdif rmspecsqrnq
      vex adantr simprl xp1st nn0ssq sseli xp2nd simprr syl122anc biimpd xpopth
      cc zq qirropth adantl sylibd sylbid ralrimivva dff1o6 syl3anbrc ) AUBUCFG
      ZCHIUDZCJZKFZAUBUALUEUFLUGFZXDMFZNLZOLZUHZXCUIZXJUJZBJZDJZXFEJZNLZOLZPZEI
      QDHQZBUKZPXNXJFZXOXJFZPZDEULZUMZEXCUNDXCUNXCXTXJUOXKXBXIUSGZXKCXCCXCXIXJU
      SXJUPZUQYFXDXCGXEXHOURUTVAUTXBXTXMXIPZCXCQZBUKXLXBXSYIBXSYIVBXBYIXSYHXRCD
      EHIXDXNXOVCZPZXIXQXMYKXEXNXHXPOYKXEYJKFXNXDYJKRXNXODWBZVDVEYKXGXOXFNYKXGY
      JMFXOXDYJMRXNXOYLEWBVFVEVGVHVIVJVKUTVLCBXCXIXJYGVMVNXBYEDEXCXCXBXNXCGZXOX
      CGZVOZVOZYCXNKFZXFXNMFZNLZOLZXOKFZXFXOMFZNLZOLZPZYDYPYAYTYBUUDYMYAYTPXBYN
      CXNXIYTXCXJCDULZXEYQXHYSOXDXNKRUUFXGYRXFNXDXNMRVGVHYGYQYSOURVPVQYNYBUUDPX
      BYMCXOXIUUDXCXJCEULZXEUUAXHUUCOXDXOKRUUGXGUUBXFNXDXOMRVGVHYGUUAUUCOURVPVR
      VSYPUUEYQUUAPYRUUBPVOZYDYPUUEUUHYPXFWMSVTGZYQSGZYRSGZUUASGZUUBSGZUUEUUHVB
      XBUUIYOAWAWCYPYMYQHGUUJXBYMYNWDZXNHIWEHSYQWFWGTYPYMYRIGUUKUUNXNHIWHYRWNTY
      PYNUUAHGUULXBYMYNWIZXOHIWEHSUUAWFWGTYPYNUUBIGUUMUUOXOHIWHUUBWNTXFYQYRUUAU
      UBWOWJWKYOUUHYDVBXBXNXOHIHIWLWPWQWRWSDEXCXTXJWTXA $.
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
       strengthening.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
    frmx $p |- rmX : ( ( ZZ>= ` 2 ) X. ZZ ) --> NN0 $=
      ( va vb vc cv c2 cexp co c1 cmin csqr cfv caddc cn0 cz cxp c1st c2nd wcel
      wral crmx cmul cmpt ccnv cuz wf wa rmxyelxp xp1st rgen2 df-rmx fmpt2 mpbi
      syl ) ADZUNEFGHIGJKZLGBDZFGCMNOZCDZPKUOURQKUAGLGUBUCKZPKZMRZBNSAEUDKZSVBN
      OMTUEVAABVBNUNVBRUPNRUFUSUQRVAUNUPCUGUSMNUHUMUIABVBNUTMTBACUJUKUL $.
      $( [22-Sep-2014] $)

    $( The Y sequence is an integer.  (Contributed by Stefan O'Rear,
       22-Sep-2014.) $)
    frmy $p |- rmY : ( ( ZZ>= ` 2 ) X. ZZ ) --> ZZ $=
      ( va vb vc cv c2 cexp co c1 cmin csqr cfv caddc cn0 cz cxp c1st c2nd wcel
      wral crmy cmul cmpt ccnv cuz wf wa rmxyelxp xp2nd rgen2 df-rmy fmpt2 mpbi
      syl ) ADZUNEFGHIGJKZLGBDZFGCMNOZCDZPKUOURQKUAGLGUBUCKZQKZNRZBNSAEUDKZSVBN
      ONTUEVAABVBNUNVBRUPNRUFUSUQRVAUNUPCUGUSMNUHUMUIABVBNUTNTBACUJUKUL $.
      $( [22-Sep-2014] $)
  $}

  ${
    $d a b c d A $.  $d a b c N $.
    $( Main definition of the X and Y sequences.  Compare definition 2.3 of
       [JonesMatijasevic] p. 694.  (Contributed by Stefan O'Rear,
       19-Oct-2014.) $)
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

  $( The discriminant used to define the X and Y sequences is a positive real.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
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
       corresponding Pell equation in the right half-plane.  (Contributed by
       Stefan O'Rear, 22-Sep-2014.) $)
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
       equation.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
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

  $( The base of exponentiation for the X and Y sequences is a positive real.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmbaserp $p |- ( A e. ( ZZ>= ` 2 ) -> ( A + ( sqr ` ( ( A ^ 2 ) - 1 ) ) ) e.
      RR+ ) $=
    ( c2 cuz cfv wcel cexp co c1 cmin cpellfund csqr caddc rmspecfund csquarenn
    crp cn cdif rmspecnonsq pellfundrp syl eqeltrrd ) ABCDEZABFGHIGZJDZAUCKDLGO
    AMUBUCPNQEUDOEARUCSTUA $.
    $( [22-Sep-2014] $)

  $( Negation law for X and Y sequences.  JonesMatijasevic is inconsistent on
     whether the X and Y sequences have domain ` NN0 ` or ` ZZ ` ; we use
     ` ZZ ` consistently to avoid the need for a separate subtraction law.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
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
     most uses.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
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

  $( Value of the X and Y sequences at 1.  (Contributed by Stefan O'Rear,
     22-Sep-2014.) $)
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

  $( Value of the X and Y sequences at 0.  (Contributed by Stefan O'Rear,
     22-Sep-2014.) $)
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
     cases.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX -u N ) = ( A rmX N
      ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simpld ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.
    $( [22-Sep-2014] $)

  $( Value of X sequence at 0.  Part 1 of equation 2.11 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmx0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 0 ) = 1 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simpld ) ABCDEAFGHIJAFKHFJ
    ALM $.
    $( [22-Sep-2014] $)

  $( Value of X sequence at 1.  Part 2 of equation 2.11 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmx1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 1 ) = A ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simpld ) ABCDEAFGHAIAFJHFIAKL
    $.
    $( [22-Sep-2014] $)

  $( Addition formula for X sequence.  Equation 2.7 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmX ( M + N ) ) = ( ( ( A rmX M ) x. ( A rmX N ) ) + ( ( ( A ^ 2 )
      - 1 ) x. ( ( A rmY M ) x. ( A rmY N ) ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simpld
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.
    $( [22-Sep-2014] $)

  $( Negation formula for Y sequence (odd function).  (Contributed by Stefan
     O'Rear, 22-Sep-2014.) $)
  rmyneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY -u N ) = -u ( A
      rmY N ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simprd ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.
    $( [22-Sep-2014] $)

  $( Value of Y sequence at 0.  Part 1 of equation 2.12 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmy0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 0 ) = 0 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simprd ) ABCDEAFGHIJAFKHFJ
    ALM $.
    $( [22-Sep-2014] $)

  $( Value of Y sequence at 1.  Part 2 of equation 2.12 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmy1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 1 ) = 1 ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simprd ) ABCDEAFGHAIAFJHFIAKL
    $.
    $( [22-Sep-2014] $)

  $( Addition formula for Y sequence.  Equation 2.8 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmyadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M )
      x. ( A rmY N ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simprd
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.
    $( [22-Sep-2014] $)

  $( Special addition-of-1 formula for X sequence.  Part 1 of equation 2.9 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     19-Oct-2014.) $)
  rmxp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmX ( N + 1 ) ) = ( ( ( A rmX N ) x. A ) + ( ( ( A ^ 2 ) - 1 ) x. (
      A rmY N ) ) ) ) $=
    ( c2 cuz wcel cz wa c1 caddc co crmx cmul cexp cmin crmy wceq adantr oveq2d
    cfv eqtrd 1z rmxadd mp3an3 rmx1 rmy1 cc frmy fovcl zcn mulid1 3syl oveq12d
    ) ACDSZEZBFEZGZABHIJKJZABKJZAHKJZLJZACMJHNJZABOJZAHOJZLJZLJZIJZURALJZVAVBLJ
    ZIJUNUOHFEUQVFPUAABHUBUCUPUTVGVEVHIUPUSAURLUNUSAPUOAUDQRUPVDVBVALUPVDVBHLJZ
    VBUNVDVIPUOUNVCHVBLAUERQUPVBFEVBUFEVIVBPABFUMFOUGUHVBUIVBUJUKTRULT $.
    $( [19-Oct-2014] $)

  $( Special addition of 1 formula for Y sequence.  Part 2 of equation 2.9 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     24-Sep-2014.) $)
  rmyp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmY ( N + 1 ) ) = ( ( ( A rmY N ) x. A ) + ( A rmX N ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc co crmy crmx cmul wceq oveq2d adantr eqtrd
    1z cn0 rmyadd mp3an3 rmx1 rmy1 cc frmx fovcl nn0cn mulid1 3syl oveq12d ) AC
    DEZFZBGFZHZABIJKLKZABLKZAIMKZNKZABMKZAILKZNKZJKZUQANKZUTJKUMUNIGFUPVCOSABIU
    AUBUOUSVDVBUTJUMUSVDOUNUMURAUQNAUCPQUOVBUTINKZUTUMVBVEOUNUMVAIUTNAUDPQUOUTT
    FUTUEFVEUTOABTULGMUFUGUTUHUTUIUJRUKR $.
    $( [24-Sep-2014] $)

  $( Subtraction of 1 formula for X sequence.  Part 1 of equation 2.10 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     14-Oct-2014.) $)
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

  $( Subtraction of 1 formula for Y sequence.  Part 2 of equation 2.10 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     19-Oct-2014.) $)
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
     Part 3 of equation 2.11 of [JonesMatijasevic] p. 695.  (Contributed by
     Stefan O'Rear, 14-Oct-2014.) $)
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
     recurrence with ~ rmy0 and ~ rmy1 .  Part 3 of equation 2.12 of
     [JonesMatijasevic] p. 695.  JonesMatijasevic uses this theorem to redefine
     the X and Y sequences to have domain ` ( ZZ X. ZZ ) ` , which simplifies
     some later theorems.  It may shorten the derivation to use this as our
     initial definition.  Incidentally, the X sequence satisfies the exact same
     recurrence.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
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

  $( Lucas sequence property of Y with better output ordering.  (Contributed by
     Stefan O'Rear, 16-Oct-2014.) $)
  rmyluc2 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) =
        ( ( ( 2 x. A ) x. ( A rmY N ) ) - ( A rmY ( N - 1 ) ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc co crmy cmul cmin rmyluc wceq frmy zcn syl
    cc fovcl eluzelz adantr mulcom syl2anc oveq2d 2cn a1i mulass syl3anc eqtr4d
    oveq1d eqtrd ) ACDEZFZBGFZHZABIJKLKCABLKZAMKZMKZABINKLKZNKCAMKURMKZVANKABOU
    QUTVBVANUQUTCAURMKZMKZVBUQUSVCCMUQURTFZATFZUSVCPUQURGFVEABGUNGLQUAURRSZUOVF
    UPUOAGFVFCAUBARSUCZURAUDUEUFUQCTFZVFVEVBVDPVIUQUGUHVHVGCAURUIUJUKULUM $.
    $( [16-Oct-2014] $)

  $( "Double-angle formula" for X-values.  Equation 2.13 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
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

  $( "Double-angle formula" for Y-values.  Equation 2.14 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
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
       adjacent pair is globally strictly monotonic by induction.  (Contributed
       by Stefan O'Rear, 24-Sep-2014.) $)
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
       ` ZZ ` .  This proof is far too long.  (Contributed by Stefan O'Rear,
       25-Sep-2014.) $)
    monotoddzzfi $p |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> ( F ` A )
        < ( F ` B ) ) ) $=
      ( cz wcel clt wbr wa cr wi eleq1d imbi12d cn0 cc0 va vb wb cv fveq2 zssre
      cfv weq eleq1 anbi2d chvarv cn cneg wo elznn simprbi anim12i adantl nnnn0
      simpll ad2antrl ad2antll w3a simpl simpr 3anbi23d breq12 breqan12d vtocl2
      vex syl3anc ex adantrr adantr 0re a1i adantrl cle wceq biimpi neg0 fveq2i
      elnn0 0z elexi negeq fveq2d negeqd eqeq12d vtocl mpan2 cc recnd eqneg syl
      syl5eqr mpbid ad2antrr nngt0 simplll 0nn0 simplrl breq12d eqbrtrrd znegcl
      negex syl2anc ltle nn0ge0i syl5breqr breq2d mpbird jaodan breqtrd le0neg1
      mpd mpdan lelttrd a1d wn simp3 c1 zre ad2antlr 1re nnre nn0ge0 1nn0 letrd
      nnge1 lenlt 3adant3 pm2.24 sylc 3exp 3com23 3expb adantlr sylibd ltneg
      3imtr4d ccased ltord1 3impb ) ADJKEJKDELMDFUGZEFUGZLMUCAUAUBUAUDZFUGZUBUD
      ZFUGZDEJUUEUUFUUGUUIFUEUUGDFUEUUGEFUEUFABUDZJKZNZUUKFUGZOKZPZAUUGJKZNZUUH
      OKZPBUABUAUHZUUMUURUUOUUSUUTUULUUQAUUKUUGJUIUJZUUTUUNUUHOUUKUUGFUEZQRGUKZ
      AUUQUUIJKZNZNZUUGULKZUUGUMZSKZUNZUUIULKZUUIUMZSKZUNZNZUUGUUILMZUUHUUJLMZP
      ZUVEUVOAUUQUVJUVDUVNUUQUUGOKZUVJUUGUOUPUVDUUIOKZUVNUUIUOUPUQURUVFUVGUVKUV
      IUVMUVRUVFUVGUVKNZUVRUVFUWANAUUGSKZUUISKZUVRAUVEUWAUTUVGUWBUVFUVKUUGUSVAU
      VKUWCUVFUVGUUIUSZVBAUUKSKZCUDZSKZVCZUUKUWFLMZUUNUWFFUGZLMZPZPZAUWBUWCVCZU
      VRPBCUUGUUIUAVJUBVJZUUTCUBUHZNZUWHUWNUWLUVRUWQUWEUWBUWGUWCAUWQUUKUUGSUUTU
      WPVDQUWQUWFUUISUUTUWPVEQVFUWQUWIUVPUWKUVQUUKUUGUWFUUILVGUUTUWPUUNUUHUWJUU
      JLUVBUWFUUIFUEZVHRRIVIVKVLUVFUVIUVKNZUVRUVFUWSNZUVQUVPUWTUUHTUUJUVFUUSUWS
      AUUQUUSUVDUVCVMZVNZTOKZUWTVOVPUVFUUJOKZUWSAUVDUXDUUQUUPAUVDNZUXDPBUBBUBUH
      ZUUMUXEUUOUXDUXFUULUVDAUUKUUIJUIUJZUXFUUNUUJOUUKUUIFUEZQRGUKVQZVNUWTUUHTV
      RMZTUUHUMZVRMZUWTTUVHFUGZUXKVRUWTUVHULKZUVHTVSZUNZTUXMVRMZUVIUXPUVFUVKUVI
      UXPUVHWCVTVAUWTUXNUXQUXOUWTUXNNZTUXMLMZUXQUXRTFUGZTUXMLUVFUXTTVSZUWSUXNAU
      YAUVEAUXTUXTUMZVSZUYAAUXTTUMZFUGZUYBUYDTFWAWBATJKZUYEUYBVSZWDUUMUUKUMZFUG
      ZUUNUMZVSZPZAUYFNZUYGPBTTOVOWEZUUKTVSZUUMUYMUYKUYGUYOUULUYFAUUKTJUIUJZUYO
      UYIUYEUYJUYBUYOUYHUYDFUUKTWFWGUYOUUNUXTUUKTFUEZWHWIRHWJWKWPAUXTWLKUYCUYAU
      CAUXTAUYFUXTOKZWDUUPUYMUYRPBTUYNUYOUUMUYMUUOUYRUYPUYOUUNUXTOUYQQRGWJWKWMU
      XTWNWOWQVNZWRUXRTUVHLMZUXTUXMLMZUXNUYTUWTUVHWSURUXRATSKZUVIUYTVUAPZAUVEUW
      SUXNWTVUBUXRXAVPUVFUVIUVKUXNXBUWMAVUBUVIVCZVUCPBCTUVHUYNUUGXFZUYOUWFUVHVS
      ZNZUWHVUDUWLVUCVUGUWEVUBUWGUVIAVUGUUKTSUYOVUFVDZQVUGUWFUVHSUYOVUFVEZQVFVU
      GUWIUYTUWKVUAUUKTUWFUVHLVGVUGUUNUXTUWJUXMLVUGUUKTFVUHWGVUGUWFUVHFVUIWGXCR
      RIVIVKXPXDUXRUXCUXMOKZUXSUXQPUXCUXRVOVPUVFVUJUWSUXNUVFAUVHJKZVUJAUVEVDUUQ
      VUKAUVDUUGXEVAUUPAVUKNZVUJPBUVHVUEUUKUVHVSZUUMVULUUOVUJVUMUULVUKAUUKUVHJU
      IUJVUMUUNUXMOUUKUVHFUEQRGWJXGWRTUXMXHXGXPUWTUXONZUXQTUXTVRMZVUNTTUXTVRTXA
      XIUVFUYAUWSUXOUYSWRXJUXOUXQVUOUCUWTUXOUXMUXTTVRUVHTFUEXKURXLXMXQUVFUXMUXK
      VSZUWSAUUQVUPUVDUYLUURVUPPBUAUUTUUMUURUYKVUPUVAUUTUYIUXMUYJUXKUUTUYHUVHFU
      UKUUGWFWGUUTUUNUUHUVBWHWIRHUKVMZVNXNUWTUUSUXJUXLUCUXBUUHXOWOXLUWTUXTTUUJL
      UVFUYAUWSUYSVNUWTTUUILMZUXTUUJLMZUVKVURUVFUVIUUIWSVBUWTAVUBUWCVURVUSPZAUV
      EUWSUTVUBUWTXAVPUVKUWCUVFUVIUWDVBUWMAVUBUWCVCZVUTPBCTUUIUYNUWOUYOUWPNZUWH
      VVAUWLVUTVVBUWEVUBUWGUWCAVVBUUKTSUYOUWPVDQVVBUWFUUISUYOUWPVEQVFVVBUWIVURU
      WKVUSUUKTUWFUUILVGUYOUWPUUNUXTUWJUUJLUYQUWRVHRRIVIVKXPXDXRXSVLUVFUVGUVMNZ
      UVPUVQUVFVVCUVPVCUVPUVPXTZUVQUVFVVCUVPYAUVFVVCVVDUVPUVFVVCNZUUIUUGVRMZVVD
      VVEUUIYBUUGUVEUVTAVVCUVDUVTUUQUUIYCURZYDZYBOKVVEYEVPZUVGUVSUVFUVMUUGYFVAZ
      VVEUUITYBVVHUXCVVEVOVPVVIVVEUUITVRMZTUVLVRMZUVMVVLUVFUVGUVLYGVBVVEUVTVVKV
      VLUCVVHUUIXOWOXLTYBVRMVVEYBYHXIVPYIUVGYBUUGVRMUVFUVMUUGYJVAYIVVEUVTUVSVVF
      VVDUCVVHVVJUUIUUGYKXGWQYLUVPUVQYMYNYOUVFUVIUVMNZUVRUVFVVMNZUVLUVHLMZUUJUM
      ZUXKLMZUVPUVQVVNVVOUVLFUGZUXMLMZVVQAVVMVVOVVSPZUVEAUVIUVMVVTAUVMUVIVVTUWM
      AUVMUVIVCZVVTPBCUVLUVHUUIXFVUEUUKUVLVSZVUFNZUWHVWAUWLVVTVWCUWEUVMUWGUVIAV
      WCUUKUVLSVWBVUFVDQVWCUWFUVHSVWBVUFVEQVFVWCUWIVVOUWKVVSUUKUVLUWFUVHLVGVWBV
      UFUUNVVRUWJUXMLUUKUVLFUEUWFUVHFUEVHRRIVIYPYQYRVVNVVRVVPUXMUXKLUVFVVRVVPVS
      ZVVMAUVDVWDUUQUYLUXEVWDPBUBUXFUUMUXEUYKVWDUXGUXFUYIVVRUYJVVPUXFUYHUVLFUUK
      UUIWFWGUXFUUNUUJUXHWHWIRHUKVQVNUVFVUPVVMVUQVNXCYSVVNUVSUVTUVPVVOUCUVFUVSV
      VMUUQUVSAUVDUUGYCVAVNUVEUVTAVVMVVGYDUUGUUIYTXGVVNUUSUXDUVQVVQUCUVFUUSVVMU
      XAVNUVFUXDVVMUXIVNUUHUUJYTXGUUAVLUUBXPUUCUUD $.
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
       monotonic on ` ZZ ` .  This proof is far too long.  (Contributed by
       Stefan O'Rear, 25-Sep-2014.) $)
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
  $}

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
       commutes with ` abs ` .  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
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
       Lucas-type sequences.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
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
       passes between adjacent integers in either direction.  (Contributed by
       Stefan O'Rear, 1-Oct-2014.) $)
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

    $( Mantissa ordering relationship for exponentiation.  (Contributed by
       Stefan O'Rear, 16-Oct-2014.) $)
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

    $( Mantissa ordering relationship for exponentiation of positive reals.
       (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
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
    $( For all nonnegative indices, X is positive and Y is nonnegative.
       (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
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
       ~ ltrmy .  (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
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
    $( The X-sequence is strictly monotonic on ` NN0 ` .  (Contributed by
       Stefan O'Rear, 4-Oct-2014.) $)
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

    $( The X-sequence is monotonic on ` NN0 ` .  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    lermxnn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M <_ N
        <-> ( A rmX M ) <_ ( A rmX N ) ) ) $=
      ( va vb c2 cuz cfv wcel cn0 cle wbr crmx co wb cv oveq2 nn0ssre cz clt wa
      cr nn0z frmx fovcl sylan2 sseldi w3a ltrmxnn0 biimpd 3expb leord1 3impb
      wi ) AFGHZIZBJICJIBCKLABMNZACMNZKLOUPDEADPZMNZAEPZMNZBCJUQURUSVAAMQUSBAMQ
      USCAMQRUPUSJIZUAJUBUTRVCUPUSSIUTJIUSUCAUSJUOSMUDUEUFUGUPVCVAJIZUSVATLZUTV
      BTLZUNUPVCVDUHVEVFAUSVAUIUJUKULUM $.
      $( [4-Oct-2014] $)

    $( The X-sequence is defined to range over ` NN0 ` but never actually takes
       the value 0.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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
    $( The Y-sequence is strictly monotonic over ` ZZ ` .  (Contributed by
       Stefan O'Rear, 25-Sep-2014.) $)
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
    $( Y is zero only at zero.  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
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
    $( Y is one-to-one.  (Contributed by Stefan O'Rear, 3-Oct-2014.) $)
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
    $( Y is monotonic (non-strict).  (Contributed by Stefan O'Rear,
       3-Oct-2014.) $)
    lermy $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> (
        A rmY M ) <_ ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel cz cle wbr crmy co wb cv oveq2 zssre wa clt fovcl
      cr frmy sseldi wi w3a ltrmy biimpd 3expb leord1 3impb ) AFGHZIZBJICJIBCKL
      ABMNZACMNZKLOUMDEADPZMNZAEPZMNZBCJUNUOUPURAMQUPBAMQUPCAMQRUMUPJIZSJUBUQRA
      UPJULJMUCUAUDUMUTURJIZUPURTLZUQUSTLZUEUMUTVAUFVBVCAUPURUGUHUIUJUK $.
      $( [3-Oct-2014] $)
  $}
  $( ` rmY ` is positive for positive arguments.  (Contributed by Stefan
     O'Rear, 16-Oct-2014.) $)
  rmynn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( A rmY N ) e. NN ) $=
    ( c2 cuz cfv wcel cn wa crmy co cz cc0 clt wbr nnz frmy fovcl sylan2 adantl
    wceq rmy0 adantr nngt0 wb simpl ltrmy syl3anc mpbid eqbrtrrd elnnz sylanbrc
    0z a1i ) ACDEZFZBGFZHZABIJZKFZLURMNURGFUPUOBKFZUSBOZABKUNKIPQRUQALIJZLURMUO
    VBLTUPAUAUBUQLBMNZVBURMNZUPVCUOBUCSUQUOLKFZUTVCVDUDUOUPUEVEUQULUMUPUTUOVASA
    LBUFUGUHUIURUJUK $.
    $( [16-Oct-2014] $)

  $( ` rmY ` is nonnegative for nonnegative arguments.  (Contributed by Stefan
     O'Rear, 16-Oct-2014.) $)
  rmynn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY N ) e. NN0 ) $=
    ( c2 cuz cfv wcel cn0 wa crmy co cz cc0 cle wbr nn0z frmy fovcl sylan2 crmx
    clt rmxypos simprd elnn0z sylanbrc ) ACDEZFZBGFZHZABIJZKFZLUIMNZUIGFUGUFBKF
    UJBOABKUEKIPQRUHLABSJTNUKABUAUBUIUCUD $.
    $( [16-Oct-2014] $)

  ${
    $d A a b $.  $d B a b $.
    $( ` rmY ` commutes with ` abs ` .  (Contributed by Stefan O'Rear,
       26-Sep-2014.) $)
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
     [JonesMatijasevic] p. 697 restricted to ` NN ` .  (Contributed by Stefan
     O'Rear, 3-Oct-2014.) $)
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
    $( First half of lemma 2.17 of [JonesMatijasevic] p. 696.  (Contributed by
       Stefan O'Rear, 14-Oct-2014.) $)
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

    $( Weak form of the second half of lemma 2.17 of [JonesMatijasevic] p. 696,
       allowing induction to start lower.  (Contributed by Stefan O'Rear,
       15-Oct-2014.) $)
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

  $( Second half of lemma 2.17 of [JonesMatijasevic] p. 696.  (Contributed by
     Stefan O'Rear, 15-Oct-2014.) $)
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

  $( Lemma 2.24 of [JonesMatijasevic] p. 697 extended to ` ZZ ` .  Could be
     eliminated with a more careful proof of ~ jm2.26lem3 .  (Contributed by
     Stefan O'Rear, 3-Oct-2014.) $)
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
       in lemma 2.27 of [JonesMatijasevic] p. 697.  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
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
     these would not need them.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A || (
      B - C ) /\ A || ( C - D ) ) ) -> A || ( B - D ) ) $=
    ( cz wcel wa co cdivides wbr w3a caddc simp1l simp1r zsubcl 3ad2ant2 cc zcn
    cmin adantl simp2l syl2anc simp3 dvds2add imp syl31anc wceq 3ad2ant1 adantr
    npncan syl3anc breqtrd ) AEFZBEFZGZCEFZDEFZGZABCSHZIJACDSHZIJGZKZAUSUTLHZBD
    SHZIVBUMUSEFZUTEFZVAAVCIJZUMUNURVAMVBUNUPVEUMUNURVANUOUPUQVAUABCOUBURUOVFVA
    CDOPUOURVAUCUMVEVFKVAVGAUSUTUDUEUFVBBQFZCQFZDQFZVCVDUGUOURVHVAUNVHUMBRTUHUR
    UOVIVAUPVIUQCRUIPURUOVJVAUQVJUPDRTPBCDUJUKUL $.
    $( [1-Oct-2014] $)

  $( If two pairs of numbers are componentwise congruent, so are their sums.
     (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
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
     products.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
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

  $( Congruence mod ` A ` is a symmetric/commutative relation.  (Contributed by
     Stefan O'Rear, 1-Oct-2014.) $)
  congsym $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( C - B ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg simprr cc wceq zcn ad2antrl ad2antlr
    negsubdi2 syl2anc breqtrrd wb simpll simprl simplr zsubcl dvdsnegb mpbird )
    ADEZBDEZFZCDEZABCGHZIJZFZFZACBGHZIJZAUPKZIJZUOAULURIUJUKUMLUOCMEZBMEZURULNU
    KUTUJUMCOPUIVAUHUNBOQCBRSTUOUHUPDEZUQUSUAUHUIUNUBUOUKUIVBUJUKUMUCUHUIUNUDCB
    UESAUPUFSUG $.
    $( [1-Oct-2014] $)

  $( If two integers are congruent mod ` A ` , so are their negatives.
     (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congneg $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( -u B - -u C ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg congsym wceq cc zcn syl2an ad2ant2lr
    neg2sub breqtrrd ) ADEZBDEZFCDEZABCGHIJZFFACBGHZBKCKGHZIABCLUAUBUEUDMZTUCUA
    BNECNEUFUBBOCOBCRPQS $.
    $( [1-Oct-2014] $)

  $( If two pairs of numbers are componentwise congruent, so are their
     differences.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
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

  $( Every integer is congruent to itself mod every base.  (Contributed by
     Stefan O'Rear, 1-Oct-2014.) $)
  congid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> A || ( B - B ) ) $=
    ( cz wcel wa cc0 cmin co cdivides wbr dvds0 adantr cc wceq zcn adantl subid
    syl breqtrrd ) ACDZBCDZEZAFBBGHZITAFIJUAAKLUBBMDZUCFNUAUDTBOPBQRS $.
    $( [1-Oct-2014] $)

  ${
    $d F a b c $.  $d X a b c k $.  $d V a b c k $.  $d Y a b c k $.
    $d N a b c k $.

    $( Polynomials commute with congruences.  (Does this characterize them?)
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
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
    $( Every integer is congruent to some number in the fundamental domain.
       (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
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
     least the congruence base.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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

  $( A wff like that in this theorem will be known as an "alternating
     congruence".  A special symbol might be considered if more uses come up.
     They have many of the same properties as normal congruences, starting with
     reflexivity.

     JonesMatijasevic uses "a &#8801; &#xB1; b (mod c)" for this construction.
     The disjunction of divisibility constraints seems to adequately capture
     the concept, but it's rather verbose and somewhat inelegant.  Use of an
     explicit equivalence relation might also work.  (Contributed by Stefan
     O'Rear, 2-Oct-2014.) $)
  acongid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A || ( B - B ) \/ A || ( B - -u B
      ) ) ) $=
    ( cz wcel wa cmin co cdivides wbr cneg congid orcd ) ACDBCDEABBFGHIABBJFGHI
    ABKL $.
    $( [2-Oct-2014] $)

  $( Symmetry of alternating congruence.  (Contributed by Stefan O'Rear,
     2-Oct-2014.) $)
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
     "alternating" part.  (Contributed by Stefan O'Rear, 3-Oct-2014.) $)
  acongneg2 $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\
          ( A || ( B - -u C ) \/ A || ( B - -u -u C ) ) ) -> ( A || ( B - C )
      \/ A || ( B - -u C ) ) ) $=
    ( cz wcel w3a cneg cmin co cdivides wbr wo wa cc zcn 3ad2ant3 negneg oveq2d
    wceq syl breq2d biimpd orim2d imp orcomd ) ADEZBDEZCDEZFZABCGZHIJKZABUJGZHI
    ZJKZLZMUKABCHIZJKZUIUOUKUQLUIUNUQUKUIUNUQUIUMUPAJUIULCBHUICNEZULCSUHUFURUGC
    OPCQTRUAUBUCUDUE $.
    $( [3-Oct-2014] $)

  $( Transitivity of alternating congruence.  (Contributed by Stefan O'Rear,
     2-Oct-2014.) $)
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
    $( Substitution deduction for alternating congruence.  (Contributed by
       Stefan O'Rear, 3-Oct-2014.) $)
    acongeq12d $p |- ( ph -> ( ( A || ( B - D ) \/ A || ( B - -u D ) ) <-> ( A
        || ( C - E ) \/ A || ( C - -u E ) ) ) ) $=
      ( cmin co cdivides wbr cneg oveq12d breq2d negeqd orbi12d ) ABCEIJZKLBDFI
      JZKLBCEMZIJZKLBDFMZIJZKLARSBKACDEFIGHNOAUAUCBKACDTUBIGAEFHPNOQ $.
      $( [3-Oct-2014] $)
  $}

  ${
    $d A a b $.  $d N a b $.
    $( Every integer is alternating-congruent to some number in the first half
       of the fundamental domain.  (Contributed by Stefan O'Rear,
       2-Oct-2014.) $)
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
     overlapping finite ranges.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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

  $( Reflection of a finite range of integers about 0.  (Contributed by Stefan
     O'Rear, 4-Oct-2014.) $)
  fzneg $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A e. ( B ... C ) <-> -u
      A e. ( -u C ... -u B ) ) ) $=
    ( cz wcel w3a cle wbr wa cneg cfz co ancom cr zre leneg syl2anc elfz znegcl
    wb 3ad2ant1 3ad2ant3 3ad2ant2 anbi12d syl5bb syl3an 3com23 3bitr4d ) ADEZBD
    EZCDEZFZBAGHZACGHZIZCJZAJZGHZUQBJZGHZIZABCKLEUQUPUSKLEZUOUNUMIULVAUMUNMULUN
    URUMUTULANEZCNEZUNURTUIUJVCUKAOUAZUKUIVDUJCOUBACPQULBNEZVCUMUTTUJUIVFUKBOUC
    VEBAPQUDUEABCRUIUKUJVBVATZUIUQDEUKUPDEUJUSDEVGASCSBSUQUPUSRUFUGUH $.
    $( [4-Oct-2014] $)

  $( Two numbers in the fundamental domain are alternating-congruent iff they
     are equal.  TODO: could be used to shorten ~ jm2.26 (Contributed by Stefan
     O'Rear, 4-Oct-2014.) $)
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

  $( Alternating congruence passes from a base to a dividing base.
     (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
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
     set the GCD, but it does upper bound it.  (Contributed by Stefan O'Rear,
     23-Sep-2014.) $)
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
     relative primality.  (Contributed by Stefan O'Rear, 23-Sep-2014.) $)
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

  $( Adding a multiple of the base does not affect divisibility.  (Contributed
     by Stefan O'Rear, 23-Sep-2014.) $)
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

  $( Multiplication by a coprime number does not affect divisibility.
     (Contributed by Stefan O'Rear, 23-Sep-2014.) $)
  coprmdvdsb $p |- ( ( K e. ZZ /\ N e. ZZ /\ ( M e. ZZ /\ ( K gcd M ) = 1 ) )
      -> ( K || N <-> K || ( M x. N ) ) ) $=
    ( cz wcel cgcd co c1 wceq wa w3a cdivides wbr simp1 simp3l simp2 dvdsmultr2
    cmul wi syl3anc simp3r coprmdvds mpan2d impbid ) ADEZCDEZBDEZABFGHIZJZKZACL
    MZABCRGLMZUJUEUGUFUKULSUEUFUINZUEUFUGUHOZUEUFUIPZABCQTUJULUHUKUEUFUGUHUAUJU
    EUGUFULUHJUKSUMUNUOABCUBTUCUD $.
    $( [23-Sep-2014] $)

  $( The absolute value of an integer is an integer.  (Contributed by Stefan
     O'Rear, 24-Sep-2014.) $)
  zabscl $p |- ( A e. ZZ -> ( abs ` A ) e. ZZ ) $=
    ( cz wcel cabs cfv cn0 nn0abscl nn0z syl ) ABCADEZFCJBCAGJHI $.
    $( [24-Sep-2014] $)

  $( The square of a natural number is a natural number.  (Contributed by
     Stefan O'Rear, 16-Oct-2014.) $)
  nn0sqcl $p |- ( A e. NN0 -> ( A ^ 2 ) e. NN0 ) $=
    ( cn0 wcel c2 cexp co 2nn0 nn0expcl mpan2 ) ABCDBCADEFBCGADHI $.
    $( [16-Oct-2014] $)

  $( Transfer divisibility to an order constraint on absolute values.
     (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
  dvdsleabs2 $p |- ( ( M e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( M || N -> ( abs ` M
      ) <_ ( abs ` N ) ) ) $=
    ( cz wcel cc0 wne w3a cdivides wbr cabs cfv cle wa zabscl 3anim1i adantr wb
    absdvdsb 3adant3 biimpa dvdsleabs sylc ex ) ACDZBCDZBEFZGZABHIZAJKZBJKLIZUG
    UHMUICDZUEUFGZUIBHIZUJUGULUHUDUKUEUFANOPUGUHUMUDUEUHUMQUFABRSTUIBUAUBUC $.
    $( [24-Sep-2014] $)

  $( Divisibility in terms of modular reduction by the absolute value of the
     base.  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
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
     base.  (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
  dvdsabsmod0 $p |- ( ( M e. ZZ /\ N e. ZZ /\ M =/= 0 ) -> ( M || N <-> ( N mod
      ( abs ` M ) ) = 0 ) ) $=
    ( cz wcel cc0 wne w3a cdivides wbr cabs cfv cmin co cmo wb absdvdsb 3adant3
    wceq cc zcn 3ad2ant2 subid1 syl breq2d bitr4d nnabscl 3adant2 simp2 moddvds
    cn 0z a1i syl3anc crp nnrp 0mod 3syl eqeq2d 3bitr2d ) ACDZBCDZAEFZGZABHIZAJ
    KZBELMZHIZBVENMZEVENMZRZVHERVCVDVEBHIZVGUTVAVDVKOVBABPQVCVFBVEHVCBSDZVFBRVA
    UTVLVBBTUABUBUCUDUEVCVEUJDZVAECDZVJVGOUTVBVMVAAUFUGZUTVAVBUHVNVCUKULBEVEUIU
    MVCVIEVHVCVMVEUNDVIERVOVEUOVEUPUQURUS $.
    $( [24-Sep-2014] $)

  $( Relative primality passes to asymmetric powers.  (Contributed by Stefan
     O'Rear, 27-Sep-2014.) $)
  rpexp1i $p |- ( ( A e. ZZ /\ B e. ZZ /\ M e. NN0 ) -> ( ( A gcd B ) = 1 -> (
      ( A ^ M ) gcd B ) = 1 ) ) $=
    ( cz wcel cn0 cgcd co c1 wceq cexp wi wa cn cc0 wo elnn0 w3a rpexp eqtrd cc
    biimprd 3expa simpr oveq2d zcn ad2antrr exp0 syl oveq1d ad2antlr a1d jaodan
    1gcd sylan2b 3impa ) ADEZBDEZCFEZABGHIJZACKHZBGHZIJZLZUSUQURMZCNEZCOJZPVDCQ
    VEVFVDVGUQURVFVDUQURVFRVCUTABCSUBUCVEVGMZVCUTVHVBIBGHZIVHVAIBGVHVAAOKHZIVHC
    OAKVEVGUDUEVHAUAEZVJIJUQVKURVGAUFUGAUHUITUJURVIIJUQVGBUNUKTULUMUOUP $.
    $( [27-Sep-2014] $)

  $( Relative primality passes to symmetric powers.  (Contributed by Stefan
     O'Rear, 27-Sep-2014.) $)
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
    $( ~ divalgmod using a class variable.  (Contributed by Stefan O'Rear,
       17-Oct-2014.) $)
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
    $( Theorem 2.18 of [JonesMatijasevic] p. 696.  Direct relationship of the
       exponential function to X and Y sequences.  (Contributed by Stefan
       O'Rear, 14-Oct-2014.) $)
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

  $( Lemma for ~ jm2.19 .  X and Y values are coprime. $)
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

  $( Lemma for ~ jm2.19 .  Extend to ZZ by symmetry.  TODO: use ~ zindbi . $)
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

  $( Lemma 2.19 of [JonesMatijasevic] p. 696.  Transfer divisibility
     constraints between Y-values and their indices.  (Contributed by Stefan
     O'Rear, 24-Sep-2014.) $)
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

  $( Lemma for ~ jm2.20nn .  Express X and Y values as a binomial. $)
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
    $( Lemma for ~ jm2.20nn .  Applying binomial theorem and taking irrational
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
    $( Lemma for ~ jm2.20nn .  Truncate binomial expansion p-adicly. $)
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

  $( Lemma 2.20 of [JonesMatijasevic] p. 696, the "first step down lemma".
     (Contributed by Stefan O'Rear, 27-Sep-2014.) $)
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

  $( Lemma for ~ jm2.26 .  Use ~ acongrep to find K', M' ~~ K, M in [ 0,N ].
     thus Y(K') ~~ Y(M') and both are small; K' = M' on pain of contradicting
     2.24, so K ~~ M $)
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
    $( Lemma 2.26 of [JonesMatijasevic] p. 697, the "second step down lemma".
       (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
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
    $( Lemma 2.15 of [JonesMatijasevic] p. 695. ` rmY ` is a polynomial for
       fixed N, so has the expected congruence property.  (Contributed by
       Stefan O'Rear, 1-Oct-2014.) $)
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

  ${
    $d a b A $.  $d a b N $.
    $( Lemma 2.16 of [JonesMatijasevic] p. 695.  This may be regarded as a
       special case of ~ jm2.15nn0 if ` rmY ` is redefined as described in
       ~ rmyluc .  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
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
          caddc simprr jm2.27a exp32 rexlimdv mpd ) AEBULUOZUPUQURZDBWQUSUQURZU
          TZULVAVBZDBCUSUQURZAEVCVDUQBVCVDUQVIVEUQZDVCVDUQZVFUQVEUQVIURZXAUBABV
          CVGVJZVHZEVKVHZDVAVHZXEXAVLLOADWAVHZXINDVMVNBULEDVOVPVQAWTXBULVAAWQVA
          VHZWTXBAXKWTUTZUTZGBUMUOZUPUQURZFBXNUSUQURZUTZUMVAVBZXBXMGVCVDUQXCFVC
          VDUQVFUQVEUQVIURZXRAXSXLUCVRXMXGGVKVHZFVAVHZXSXRVLAXGXLLVRAXTXLQVRAYA
          XLAFVKVHZYAPFVSVNVRBUMGFVOVPVQXMXQXBUMVAXMXNVAVHZXQXBXMYCXQUTZUTZJHUN
          UOZUPUQURZIHYFUSUQURZUTZUNVAVBZXBYEJVCVDUQHVCVDUQVIVEUQIVCVDUQVFUQVEU
          QVIURZYJAYKXLYDUEVTYEHXFVHZJVKVHZIVAVHZYKYJVLAYLXLYDUDVTAYMXLYDTVTAYN
          XLYDAIVKVHZYNSIVSVNVTHUNJIVOVPVQYEYIXBUNVAYEYFVAVHZYIXBYEYPYIUTZUTBCD
          EWQXNYFFGHIJKAXGXLYDYQLWBACWAVHXLYDYQMWBAXJXLYDYQNWBAXHXLYDYQOWBAYBXL
          YDYQPWBAXTXLYDYQQWBAHVKVHXLYDYQRWBAYOXLYDYQSWBAYMXLYDYQTWBAKVKVHXLYDY
          QUAWBAXEXLYDYQUBWBAXSXLYDYQUCWBAYLXLYDYQUDWBAYKXLYDYQUEWBAFKVIWKUQVCX
          DVFUQVFUQURXLYDYQUFWBAGHBVEUQWCWDXLYDYQUGWBAVCDVFUQZHVIVEUQWCWDXLYDYQ
          UHWBAGIDVEUQWCWDXLYDYQUIWBAYRICVEUQWCWDXLYDYQUJWBACDWEWDXLYDYQUKWBXMX
          KYDYQAXKWTWFVTXMWRYDYQAXKWRWSWGVTXMWSYDYQAXKWRWSWHVTXMYCXQYQWIYDXOXMY
          QYCXOXPWFWJYDXPXMYQYCXOXPWLWJYEYPYIWFYEYPYGYHWGYEYPYGYHWHWMWNWOWPWNWO
          WPWNWOWP $.
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

    $( Lemma 2.27 of [JonesMatijasevic] p. 697; rmY is a diophantine relation.
       0 was excluded from the range of B and the lower limit of G was imposed
       because the source proof does not seem to work otherwise; quite possible
       I'm just missing something.  The source proof uses both i and I; i has
       been changed to j to avoid collision.  This theorem is basically nothing
       but substitution instances, all the work is done in ~ jm2.27a and
       ~ jm2.27c .  Once Diophantine relations have been defined, the content
       of the theorem is "rmY is Diophantine" (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
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

    $( ~ jm2.27 restated in terms of Diophantine sets.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.) $)
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
    $( X is a Diophantine function.  (Contributed by Stefan O'Rear,
       17-Oct-2014.) $)
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
       [JonesMatijasevic] p. 698.  (Contributed by Stefan O'Rear,
       16-Oct-2014.) $)
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
       is sometimes regarded as Matiyasevich's theorem properly.  (Contributed
       by Stefan O'Rear, 17-Oct-2014.) $)
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
       Infinity.  (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
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
       ~ setindtr .  (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
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

    $( Ordinals are precisely the hereditarily transitive classes.
       (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
    dford3 $p |- ( Ord N <-> ( Tr N /\ A. x e. N Tr x ) ) $=
      ( va word wtr cv wral wa ordtr wcel ordelord syl ralrimiva jca con0 simpl
      wss dford3lem1 dford3lem2 ralimi dfss3 biimpri 3syl ordon trssord syl3anc
      a1i impbii ) BDZBEZAFZEZABGZHZUIUJUMBIUIULABUIUKBJHUKDULBUKKUKILMNUNUJBOQ
      ZODZUIUJUMPUNCFZEULAUQGHZCBGUQOJZCBGZUOABCRURUSCBCASTUOUTCBOUAUBUCUPUNUDU
      GBOUEUFUH $.
      $( [28-Oct-2014] $)

    $( ~ dford3 expressed in primitives to demonstrate shortness.  (Contributed
       by Stefan O'Rear, 28-Oct-2014.) $)
    dford4 $p |- ( Ord N <-> A. a A. b A. c ( ( a e. N /\ b e. a ) ->
        ( b e. N /\ ( c e. b -> c e. a ) ) ) ) $=
      ( wtr cv wa wel wi wal dftr2 ax-17 ancom imbi1i bitri 2albii alcom bitr4i
      wcel impexp word wral dford3 df-ral imbi2i 19.21-2 anbi2i 3bitr3i 3bitr2i
      19.3 anass albii anbi12i 19.26 19.26-2 pm4.76 bitr3i 3bitri ) AUAAEZBFZEZ
      BAUBZGZUTASZCBHZGZCFASZIZDJZCJZVFDCHZDBHZIZIZDJCJZGZBJZVFVGVMGIZDJCJZBJBA
      UCVCVJBJZVOBJZGVQUSVTVBWAUSVEVDGZVGIZBJCJZVTCBAKVTWCCJBJWDVIWCBCVIVHWCVHD
      VHDLUJVFWBVGVDVEMNOPWCBCQORVBVDVAIZBJWAVABAUDWEVOBWEVDVKVEGZVLIZCJDJZIVDW
      GIZCJDJZVOVAWHVDDCUTKUEVDWGDCVDDLVDCLUFWJVNCJDJVOWIVNDCVDWFGZVLIVFVKGZVLI
      WIVNWKWLVLWKVDVEVKGZGWLWFWMVDVKVEMUGVDVEVKUKRNVDWFVLTVFVKVLTUHPVNDCQOUIUL
      OUMVJVOBUNRVPVSBVPVHVNGZDJCJVSVHVNCDUOWNVRCDVFVGVMUPPUQULUR $.
      $( [28-Oct-2014] $)
  $}

  ${
    $d ph y $.  $d x y $.  $d A y a $.
    $( Two ways to express "exactly one".  (Contributed by Stefan O'Rear,
       28-Oct-2014.) $)
    reuen1 $p |- ( E! x e. A ph <-> { x e. A | ph } ~~ 1o ) $=
      ( vy wreu crab cv csn wceq wex c1o cen wbr reusn en1 bitr4i ) ABCEABCFZDG
      HIDJQKLMABDCNDQOP $.
      $( [28-Oct-2014] $)

    $( Two ways to express "exactly one".  (Contributed by Stefan O'Rear,
       28-Oct-2014.) $)
    euen1 $p |- ( E! x ph <-> { x | ph } ~~ 1o ) $=
      ( cvv wreu crab c1o cen wbr weu cab reuen1 reuv rabab breq1i 3bitr3i ) AB
      CDABCEZFGHABIABJZFGHABCKABLPQFGABMNO $.
      $( [28-Oct-2014] $)

    $( A set has less than one member iff it is empty.  (Contributed by Stefan
       O'Rear, 28-Oct-2014.) $)
    sdom1 $p |- ( A ~< 1o <-> A = (/) ) $=
      ( va c1o csdm wbr c0 wceq wcel relsdom brrelexi cv wi breq1 eqeq1 imbi12d
      cvv wn cdom domnsym 0sdom con2i 0sdom1dom sylnibr necon2bbii sylibr mpcom
      vex vtoclg wne 1n0 con0 1on elexi mpbir mpbiri impbii ) ACDEZAFGZAPHUQURA
      CDIJBKZCDEZUSFGZLUQURLBAPUSAGUTUQVAURUSACDMUSAFNOUTFUSDEZQVAUTCUSREZVBVCU
      TCUSSUAUSBUGZUBUCVBUSFUSVDTUDUEUHUFURUQFCDEZVECFUIUJCCUKULUMTUNAFCDMUOUP
      $.
      $( [28-Oct-2014] $)

    $( Two ways to express "at most one".  (Contributed by Stefan O'Rear,
       28-Oct-2014.) $)
    modom $p |- ( E* x ph <-> { x | ph } ~<_ 1o ) $=
      ( wmo wex weu wi wn cab c1o cdom wbr df-mo imor csdm cen wceq abn0 bitr4i
      wo c0 necon1bbii sdom1 euen1 orbi12i brdom2 3bitri ) ABCABDZABEZFUGGZUHSZ
      ABHZIJKZABLUGUHMUJUKINKZUKIOKZSULUIUMUHUNUIUKTPUMUGUKTABQUAUKUBRABUCUDUKI
      UERUF $.
      $( [28-Oct-2014] $)
  $}

  $( Unrelated:  Wiener pairs treat proper classes symmetrically.  (Contributed
     by Stefan O'Rear, 19-Sep-2014.) $)
  wopprc $p |- ( ( A e. _V /\ B e. _V ) <-> -. 1o e. { { { A } , (/) } , { { B
      } } } ) $=
    ( cvv wcel wa c0 csn cpr c1o wceq wn wo pm4.56 dfsn2 snex 0ex snprc con2bii
    impbii xchbinxr id syl5reqr preqr1 syl sylibr biimpi preq1d syl6reqr bitr2i
    eqcom sneqr sneq anbi12i elpr notbii 3bitr4i df1o2 eleq1i ) ACDZBCDZEZFGZAG
    ZFHZBGZGZHZDZIVGDVBVDJZKZVBVFJZKZEVIVKLZKVAVHKVIVKMUSVJUTVLVIUSVIUSKZVIVCFJ
    ZVNVIVDFFHZJVOVIVPVBVDFNZVIUAUBVCFFAOPUCUDAQZUEVNVDVPVBVNVCFFVNVOVRUFUGVQUH
    SRUTFVEJZVKVSUTUTKVEFJVSBQVEFUJUIRVKVSFVEPUKFVEULSTUMVHVMVBVDVFFOUNUOUPIVBV
    GUQURT $.
    $( [19-Sep-2014] $)

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
      syl21anc incom eqeq1i wral disj eleq1 notbid rcla4cv sylbi wf f1of simplr
      mpd syl ad2antrr ffvelrn syl2anc elun sylib orel1 sylc ex weq wb ad2antrl
      wf1 f1of1 ad2antll jca f1fveq opth1 syl6bi opeq1 fveq2d impbid1 dom2d mpi
      adantr necon3bd 3adant2 ) CHZBHZIJKZAHZXIXJUAZLZMZXIXJUBUCZNZXMXMUDZXMDHZ
      UEZUFXQXIXSXIXLUGZUDZUHZIZJUIZXOXQXTUJXOXTXQYEOXQXOXTMZXPYDJYFYDJKZXPYFYG
      MZXIUKLXPCPYHEFXIXJEHZXLULZXSUQZFHZXLULZXSUQZUKYHECQZYKXJLZYHYOMZYKXILZNZ
      YRYPUMZYPYQYKYCLZYSYFYOUUAYGYFYOMZXSUNZYJXSURZLZYJYBLZUUAXTUUCXOYOXRXMXSU
      ORUUBYJXRUUDUUBYIXMLZXNYJXRLZYOUUGYFYIXIXJUPZUSXKXNXTYOUTYIXLXMXMAPZSZTXT
      UUDXRKXOYOXRXMXSVARVBUUBYOXLYALZUUFYFYOVCUULUUBXLUUJVDVEYIXLXIYAUUJSTUUCU
      UEMUUFUUAYBYJXSVFVGVIVHYGUUAYSOZYFYOYGYCXIIZJKZUUMYDUUNJXIYCVJVKUUOGCQZNZ
      GYCVLUUMGYCXIVMUUQYSGYKYCGHZYKKUUPYRUURYKXIVNVOVPVQVQRWAYQYKXMLZYTYQXRXMX
      SVRZUUHUUSYQXTUUTXOXTYGYOUTXRXMXSVSWBYQUUGXNUUHYOUUGYHUUIUSYFXNYGYOXKXNXT
      VTWCUUKTXRXMYJXSWDWEYKXIXJWFWGYRYPWHWIWJYFYOFCQZMZYKYNKZEFWKZWLZOYGYFUVBU
      VEYFUVBMZUVCUVDUVFUVCYJYMKZUVDUVFXRXMXSWNZUUHYMXRLZMZUVCUVGWLXTUVHXOUVBXR
      XMXSWORXOUVBUVJXTXOUVBMZUUHUVIUVKUUGXNUUHYOUUGXOUVAUUIWMXKXNUVBVTZUUKTUVK
      YLXMLZXNUVIUVAUVMXOYOYLXIXJUPWPUVLYLXLXMXMUUJSTWQVHXRXMYJYMXSWRWEYIXLYLXL
      EPWSWTUVDYJYMXSYIYLXLXAXBXCWJXFXDXEWJXGXHWA $.
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
      ( vd cv wceq cdom wbr wn wcel com cxp cen wi wa cvv wss vex wex breq2 cin
      cfn w3a con0 wal cun unex simpl2 wral isinf weq anbi2d exbidv rcla4cv syl
      3ad2ant3 ensym ssdomg ax-mp endomtr syl2anr exlimiv syl6 adantr mtod word
      c0 wb ordom eloni adantl ordtri1 sylancr mpbird ssun1 syl6ss mpsyl xpeq12
      ssdom2g anidms id breq12d imbi12d cla4v syl5com wf1o bren simpll1 simpll2
      simpr simplr ttaclem5 syl31anc ex exlimdv syl5bi syld impr ) BEZAEZUAVGFZ
      WSWTGHZIZWTUBJIZUCZWSUDJZKCEZGHZXGXGLZXGMHZNZCUEZWTWSGHZXEXFOZXLWSWTUFZXO
      LZXOMHZXMXNKXOGHZXLXQXOPJXNKXOQXRWSWTBRZARUGZXNKWSXOXNKWSQZWSKJZIZXNYBXBX
      AXCXDXFUHXEYBXBNXFXEYBDEZWTQZYDWSMHZOZDSZXBXDXAYBYHNZXCXDYEYDXGMHZOZDSZCK
      UIYIDWTCUJYLYHCWSKCBUKZYKYGDYMYJYFYEXGWSYDMTULUMUNUOUPYGXBDYFWSYDMHYDWTGH
      ZXBYEYDWSXSUQYDPJYEYNNDRYDWTPURUSWSYDWTUTVAVBVCVDVEXNKVFWSVFZYAYCVHVIXFYO
      XEWSVJVKKWSVLVMVNWSWTVOVPKXOPVSVQXKXRXQNCXOXTXGXOFZXHXRXJXQXGXOKGTYPXIXPX
      GXOMYPXIXPFXGXOXGXOVRVTYPWAWBWCWDWEXQXPXOXGWFZCSXNXMXPXOCXTWGXNYQXMCXNYQX
      MXNYQOXAXCYQXFXMXAXCXDXFYQWHXAXCXDXFYQWIXNYQWJXEXFYQWKABCWLWMWNWOWPWQWR
      $.
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

    $( Tarski's theorem about choice: ~ infxpidm is equivalent to ~ ax-ac .
       (Contributed by Stefan O'Rear, 4-Nov-2014.) $)
    ttac $p |- ( A. a E. b b We a <-> A. c ( om ~<_ c -> ( c X. c ) ~~ c ) ) $=
      ( vd cv wwe wex wal cen wbr con0 wrex com cdom cxp cvv wcel vex alrimiv
      wi wb ween ax-mp albii cfn wn weq breq2 rexbidv domnsym isfinite3 sylnibr
      a4v csdm infxpidm2 ex syl2im ttaclem8 impbii bitri ) AEZBEFBGZAHDEZVAIJZD
      KLZAHZMCEZNJZVGVGOVGIJZTZCHZVBVEAVAPQVBVEUAARDVAPBUBUCUDVFVKVFVJCVFVCVGIJ
      ZDKLZVHVGUEQZUFZVIVEVMACACUGVDVLDKVAVGVCIUHUIUMVHVGMUNJVNMVGUJVGUKULVMVOV
      IDVGCRUOUPUQSVKVEAADCURSUSUT $.
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

    $( The proper subset relation is a relation.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
    relrpss $p |- Rel {C.} $=
      ( va vb cv wpss crpss df-rpss relopabi ) ACBCDABEABFG $.
      $( [2-Nov-2014] $)

    ${
      $( The proper subset relation on sets is the same as class proper
         subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
      brrpssg $p |- ( B e. _V -> ( A {C.} B <-> A C. B ) ) $=
        ( va vb cvv wcel crpss wbr wpss relrpss brrelexi adantl simpl jca pssss
        wa wss id ssexg cv syl2anr psseq1 psseq2 df-rpss brabg pm5.21nd ) BEFZA
        BGHZABIZAEFZUGPUGUHPUJUGUHUJUGABGJKLUGUHMNUGUIPUJUGUIABQUGUJUGABOUGRABE
        SUAUGUIMNCTZDTZIAULIUICDABEEGUKAULUBULBAUCCDUDUEUF $.
        $( [2-Nov-2014] $)

      brrpss.a $e |- B e. _V $.
      $( The proper subset relation on sets is the same as class proper
         subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
      brrpss $p |- ( A {C.} B <-> A C. B ) $=
        ( cvv wcel crpss wbr wpss wb brrpssg ax-mp ) BDEABFGABHICABJK $.
        $( [2-Nov-2014] $)
    $}

    $( Every class is partially ordered by proper subsets.  (Contributed by
       Stefan O'Rear, 2-Nov-2014.) $)
    porpss $p |- {C.} Po A $=
      ( va vb vc crpss wpo cv wbr wn wa wi wral wpss vex brrpss anbi12i imbi12i
      notbii pssirr psstr mpbir2an rgenw rgen2w df-po mpbir ) AEFBGZUFEHZIZUFCG
      ZEHZUIDGZEHZJZUFUKEHZKZJZDALZCALBALUQBCAAUPDAUPUFUFMZIZUFUIMZUIUKMZJZUFUK
      MZKZUHUSUOVDUGURUFUFBNORUMVBUNVCUJUTULVAUFUICNOUIUKDNZOPUFUKVEOQPUFSUFUIU
      KTUAUBUCBCDAEUDUE $.
      $( [2-Nov-2014] $)

    $( Express strict ordering under proper subsets, i.e. the notion of a chain
       of sets.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    sorpss $p |- ( {C.} Or A <-> A. x e. A A. y e. A ( x C_ y \/
        y C_ x ) ) $=
      ( cv crpss wbr weq w3o wral wpo wss wor porpss biantrur wpss sspsstri vex
      wa wo brrpss biid 3orbi123i bitr4i 2ralbii df-so 3bitr4ri ) ADZBDZEFZABGZ
      UHUGEFZHZBCIACIZCEJZUMRUGUHKUHUGKSZBCIACICELUNUMCMNUOULABCCUOUGUHOZUJUHUG
      OZHULUGUHPUIUPUJUJUKUQUGUHBQTUJUAUHUGAQTUBUCUDABCEUEUF $.
      $( [2-Nov-2014] $)

    $( Property of a chain of sets.  (Contributed by Stefan O'Rear,
       2-Nov-2014.) $)
    sorpssi $p |- ( ( {C.} Or A /\ ( B e. A /\ C e. A ) ) ->
        ( B C_ C \/ C C_ B ) ) $=
      ( crpss wor wcel wa wpss wceq w3o wss wbr solin cvv elex ad2antll brrpssg
      wo wb syl biidd ad2antrl 3orbi123d mpbid sspsstri sylibr ) ADEZBAFZCAFZGG
      ZBCHZBCIZCBHZJZBCKCBKRUJBCDLZULCBDLZJUNABCDMUJUOUKULULUPUMUJCNFZUOUKSUIUQ
      UGUHCAOPBCQTUJULUAUJBNFZUPUMSUHURUGUIBAOUBCBQTUCUDBCUEUF $.
      $( [2-Nov-2014] $)

    $d F a b c d e f $.  $d R a b c d e f $.
    $( The range of a single-step monotone function from ` om ` into a
       partially ordered set is a chain.  (Contributed by Stefan O'Rear,
       3-Nov-2014.) $)
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
    $( A set is Ia-finite iff it is not the union of two I-infinite sets.
       Definition Ia of [Levy] p. 2.  This is the second of Levy's eight
       definitions of finite set.  Levy's I-finite is equivalent to our
       ~ df-fin and not repeated here.  These eight definitions are equivalent
       with Choice but strictly decreasing in strength in models where Choice
       fails; conversely, they provide a series of increasingly stronger
       notions of infiniteness. $)
    df-fin1a $a |- Fin1a = { x | -. E. y E. z ( ( x = ( y u. z ) /\
      ( y i^i z ) = (/) ) /\ ( -. y e. Fin /\ -. z e. Fin ) ) } $.

    $( A set is II-finite (Tarski finite) iff every nonempty chain of subsets
       contains a maximum element.  Definition II of [Levy] p. 2. $)
    df-fin2 $a |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\
      {C.} Or y ) -> E. z e. y A. w e. y -. z C. w ) } $.

    $( A set is IV-finite (Dedekind finite) iff it has no equinumerous proper
       subset.  Definition IV of [Levy] p. 3. $)
    df-fin4 $a |- Fin4 = { x | -. E. y ( y C. x /\ y ~~ x ) } $.

    $( A set is III-finite (weakly Dedekind finite) iff its power set is
       Dedekind finite.  Definition III of [Levy] p. 2. $)
    df-fin3 $a |- Fin3 = { x | ~P x e. Fin4 } $.

    $( A set is V-finite iff it behaves finitely under ` +c ` .  Definition V
       of [Levy] p. 3. $)
    df-fin5 $a |- Fin5 = { x | ( x ~~ (/) \/ x ~< ( x +c x ) ) } $.

    $( A set is VI-finite iff it behaves finitely under ` X. ` .  Definition VI
       of [Levy] p. 4. $)
    df-fin6 $a |- Fin6 = { x | ( x ~~ (/) \/ x ~~ 1o \/ x ~< ( x X. x ) ) } $.

    $( A set is VII-finite iff it cannot be infinitely well ordered.
       Equivalent to definition VII of [Levy] p. 4. $)
    df-fin7 $a |- Fin7 = { x | -. E. y e. ( On \ om ) x ~~ y } $.
  $}

  ${
    $d A a $.  $d B a $.

    $( A finite set is strictly dominated by another iff their cardinalities
       are strictly ordered.  TODO: ~ ficarddom has a statement which is not
       consistent with related theorems.  (Contributed by Stefan O'Rear,
       30-Oct-2014.) $)
    ficardsdom $p |- ( ( A e. Fin /\ B e. Fin ) -> ( ( card ` A ) e.
      ( card ` B ) <-> A ~< B ) ) $=
      ( cfn wcel wa ccrd cfv wss wne cdom wbr wn csdm ficarddom bicomd ficarden
      cen necon3abid con0 cardon anbi12d wb onelpss mp2an brsdom 3bitr4g ) ACDB
      CDEZAFGZBFGZHZUHUIIZEZABJKZABQKZLZEUHUIDZABMKUGUJUMUKUOUGUMUJABNOUGUNUHUI
      ABPRUAUHSDUISDUPULUBATBTUHUIUCUDABUEUF $.
      $( [30-Oct-2014] $)

    $( Trichotomy of dominance without AC when one set is finite.  (Contributed
       by Stefan O'Rear, 30-Oct-2014.) $)
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
    $( Trichotomy of dominance without AC when one set is finite.  (Contributed
       by Stefan O'Rear, 30-Oct-2014.) $)
    fidomtri2 $p |- ( B e. Fin -> ( A ~<_ B <-> -. B ~< A ) ) $=
      ( cfn wcel cdom wbr csdm wn domnsym cen wa sdomdom con3i fidomtri syl5ibr
      wi ensym endom syl a1i jcad brsdom syl6ibr con1d impbid2 ) BDEZABFGZBAHGZ
      IABJUGUHUIUGUHIZBAFGZBAKGZIZLUIUGUJUKUMUJUKUGABHGZIUNUHABMNBAOPUJUMQUGULU
      HULABKGUHBACRABSTNUAUBBAUCUDUEUF $.
      $( [30-Oct-2014] $)

    $( A set with less than two elements has 0 or 1.  (Contributed by Stefan
       O'Rear, 30-Oct-2014.) $)
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
      ( vb vc cv cvv wcel com cfv wral wa wel wf1 cdom wbr vex wceq infpssrlem3
      wf weq wi wo wne simpll simplrr infpssrlem4 syl3anc necomd simplrl jaodan
      wn simpr ex necon2bd wb word nnord ordtri3 syl2an adantl ralrimivva dff13
      sylibrd sylanbrc f1dom2g mpsyl ) FMZNOAPVOEUAZPVOUBUCFUDAPVOEUGKMZEQZLMZE
      QZUEZKLUHZUIZLPRKPRVPABCDEFGHIJUFAWCKLPPAVQPOZVSPOZSZSZWAKLTZLKTZUJZUSZWB
      WGWJVRVTWGWJVRVTUKZWGWHWLWIWGWHSZVTVRWMAWEWHVTVRUKAWFWHULAWDWEWHUMWGWHUTA
      BCVSVQDEFGHIJUNUOUPWGWISAWDWIWLAWFWIULAWDWEWIUQWGWIUTABCVQVSDEFGHIJUNUOUR
      VAVBWFWBWKVCZAWDVQVDVSVDWNWEVQVEVSVEVQVSVFVGVHVKVIKLPVOEVJVLPVONEVMVN $.
      $( [30-Oct-2014] $)
  $}

  ${
    $d a x c y f A $.  $d a x c y f X $.
    infpssr.a $e |- A e. _V $.
    $( Dedekind infinity implies existance of a denumerable subset: take a
       single point witnessing the proper subset relation and iterate the
       embedding.  The hypothesis is technically redundant with our current
       ~ df-op .  (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
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

    $( Taking images under a one-to-one function preserves subsets.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
    f1imass $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C_ ( F " D ) <-> C C_ D ) ) $=
      ( va wf1 wss wa cima cv wcel wi simplrl sseld wb 3expa f1elima syl3anc ex
      simplr simplll simpr simp1rl simp1rr 3imtr3d pm2.43d ssrdv imass2 impbid1
      cfv syld ) ABEGZCAHZDAHZIZIZECJZEDJZHZCDHZUQUTVAUQUTIZFCDVBFKZCLZVCDLZVBV
      DVCALZVDVEMZVBCAVCUMUNUOUTNOVBVFVGVBVFIZVCEUKZURLZVIUSLZVDVEVHURUSVIUQUTV
      FUAOVHUMVFUNVJVDPUMUPUTVFUBZVBVFUCZUQUTVFUNUNUOUMUTVFUDQABEVCCRSVHUMVFUOV
      KVEPVLVMUQUTVFUOUNUOUMUTVFUEQABEVCDRSUFTULUGUHTCDEUIUJ $.
      $( [30-Oct-2014] $)

    $( Taking images under a one-to-one function preserves equality.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
    f1imaeq $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) = ( F " D ) <-> C = D ) ) $=
      ( wf1 wss wa cima wceq f1imass wb ancom2s anbi12d eqss 3bitr4g ) ABEFZCAG
      ZDAGZHHZECIZEDIZGZUBUAGZHCDGZDCGZHUAUBJCDJTUCUEUDUFABCDEKQSRUDUFLABDCEKMN
      UAUBOCDOP $.
      $( [30-Oct-2014] $)

    $( Taking images under a one-to-one function preserves proper subsets.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
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
      syl5ibrcom csn cdif wex difexg cuni eldifi wss ordom peano2 ordelss nnord
      sylancr orduniss wb orduni vex uniex sylibr ordsssuc syl2anc mpbid sseldd
      elon wne peano3 eldifsn sylanbrc ordunisuc eqcomd adantl unieq wrex nnsuc
      eqeq2d suceloni eleq1 imp onsucuni2 sylancom rexlimiva sylbi adantr suceq
      nnon impbid en3d peano1 cin disjsn con2bii disj4 bitr4i mpbi jctil psseq1
      wn breq1 anbi12d cla4egv sylc ) DEFZDGUAZUBZEFXCDHZXCDIJZKZALZDHZXGDIJZKZ
      AUCDXBEUDZXAXEXDXABCXCDBLZUEZCLZMZXKXLXCFZXMDFZNXAXPXLDFZXQXLDXBUFXRXLMZD
      XMXRDOXSDFXSDUGUHXLUIDXSUJULXRXMXLUGZXMXSFZXRXLOZXTXLUKZXLUMPXRXMQFZYBXTY
      AUNXRXMOZYDXRYBYEYCXLUOPXMXLBUPUQVCURYCXMXLUSUTVAVBPRXNDFZXOXCFZNXAYFXODF
      XOGVDYGXNUIXNVEXODGVFVGRXPYFKZXLXOSZXNXMSZUNNXAYHYIYJYHYJYIXNXOUEZSZYFYLX
      PYFYKXNYFXNOYKXNSXNUKXNVHPVIVJYIXMYKXNXLXOVKVNTYHYIYJXLXMMZSZXPYNYFXPXRXL
      GVDKZYNXLDGVFYOYICDVLYNCXLVMYIYNCDYFYIKYMXLYFYIXLQFZYMXLSYFYIYPYFYPYIXOQF
      ZYFXNQFYQXNWDXNVOPXLXOQVPTVQXLXNVRVSVIVTPWAWBYJXOYMXLXNXMWCVNTWERWFGDFZXD
      WGYRDXBWHGSZWPXDYSYRDGWIWJYSXDDXBWKWJWLWMWNXJXFAXCEXGXCSXHXDXIXEXGXCDWOXG
      XCDIWQWRWSWT $.
      $( [30-Oct-2014] $)

    infpssALT.a $e |- A e. _V $.
    $( A set with a denumerable subset has a proper subset equinumerous to it,
       proved without AC or Infinity.  (Contributed by Stefan O'Rear,
       30-Oct-2014.) $)
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

    $( Two ways to express overlapping subsets.  (Contributed by Stefan O'Rear,
       31-Oct-2014.) $)
    pssdifcom1 $p |- ( ( A C_ C /\ B C_ C ) ->
      ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $=
      ( wss wa cdif wpss difcom a1i ssconb ancoms notbid anbi12d dfpss3 3bitr4g
      wn wb ) ACDZBCDZEZCAFZBDZBUADZPZECBFZADZAUEDZPZEUABGUEAGTUBUFUDUHUBUFQTCA
      BHITUCUGSRUCUGQBACJKLMUABNUEANO $.
      $( [31-Oct-2014] $)

    $( Two ways to express non-covering pairs of subsets.  (Contributed by
       Stefan O'Rear, 31-Oct-2014.) $)
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

    $( ` Fin2 ` expressed in terms of minimal elements.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
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

    $( ` Fin2 ` sets contain unions for all nonempty chains.  (Contributed by
       Stefan O'Rear, 2-Nov-2014.) $)
    dffin2-3 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ {C.} Or y ) ->
        U. y e. y ) } $=
      ( va vz vw cfin2 cv c0 wne crpss wor wa cuni wcel wi cpw wral cab wpss wn
      wrex wb fin23lem4 adantl pm5.74i ralbii df-fin2 abeq2i vex weq pweq pweqd
      raleqdv elab 3bitr4i eqriv ) CFBGZHIZUQJKZLZUQMUQNZOZBAGZPZPZQZARZUTDGEGS
      TEUQQDUQUAZOZBCGZPZPZQZVBBVLQZVJFNVJVGNVIVBBVLUTVHVAUSVHVAUBUREDUQUCUDUEU
      FVMCFCBDEUGUHVFVNAVJCUIACUJZVBBVEVLVOVDVKVCVJUKULUMUNUOUP $.
      $( [2-Nov-2014] $)

    $( ` Fin2 ` sets contain intersections for all nonempty chains.
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    dffin2-4 $p |- Fin2 = { x | A. y e. ~P ~P x ( ( y =/= (/) /\ {C.} Or y ) ->
        |^| y e. y ) } $=
      ( va vw vz cfin2 cv c0 wne crpss wor wa cint wcel wi cpw wral cab wpss wn
      wrex fin23lem5 adantl pm5.74i ralbii dffin2-2 abeq2i vex weq pweq raleqdv
      wb pweqd elab 3bitr4i eqriv ) CFBGZHIZUQJKZLZUQMUQNZOZBAGZPZPZQZARZUTDGEG
      STDUQQEUQUAZOZBCGZPZPZQZVBBVLQZVJFNVJVGNVIVBBVLUTVHVAUSVHVAULURDEUQUBUCUD
      UEVMCFCBEDUFUGVFVNAVJCUHACUIZVBBVEVLVOVDVKVCVJUJUMUKUNUOUP $.
      $( [2-Nov-2014] $)

    $d a b c A $.  $d a b c B $.
    $( A subset of a II-finite set is II-finite.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
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

    $( Equality theorem for ` seqom ` .  (Contributed by Stefan O'Rear,
       1-Nov-2014.) $)
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
       numbers.  (Contributed by Stefan O'Rear, 1-Nov-2014.) $)
    fnseqom $p |- G Fn om $=
      ( va vb vd vc com wfn cvv cv csuc co cop cmpt2 c0 cid cfv crdg cima eqtri
      seqomlem0 seqomlem2 cseqom df-seqom fneq1i mpbir ) BIJEFIKELZMUIFLANOPQCR
      SOTZIUAZIJGUJHACACEFHGUCUDIBUKBACUEUKDFEACUFUBUGUH $.
      $( [1-Nov-2014] $)

    $( Value of an index-aware recursive definition at 0.  (Contributed by
       Stefan O'Rear, 1-Nov-2014.) $)
    seqom0g $p |- ( I e. _V -> ( G ` (/) ) = I ) $=
      ( va vb vd vc cvv wcel c0 cfv cid com cv csuc co cop cmpt2 eqtri df-seqom
      crdg cima cseqom fveq1i seqomlem0 seqomlem3 fvi syl5eq ) CIJKBLZCMLZCUJKE
      FNIEOZPULFOAQRSKUKRUBZNUCZLUKKBUNBACUDUNDFEACUATUEGUMHACACEFHGUFUGTCIUHUI
      $.
      $( [1-Nov-2014] $)

    $( Value of an index-aware recursive definition at a successor.
       (Contributed by Stefan O'Rear, 1-Nov-2014.) $)
    seqomsuc $p |- ( A e. om -> ( G ` suc A ) = ( A F ( G ` A ) ) ) $=
      ( va vb vd vc com wcel csuc cvv cv co cop cmpt2 c0 cfv fveq1i crdg cseqom
      cid cima seqomlem0 seqomlem4 df-seqom eqtri oveq2i 3eqtr4g ) AJKALZFGJMFN
      ZLULGNBOPQRDUCSPUAZJUDZSAAUNSZBOUKCSAACSZBOHAUMIBDBDFGIHUEUFUKCUNCBDUBUNE
      GFBDUGUHZTUPUOABACUNUQTUIUJ $.
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

    $( In a chain of finite sets, dominance and subset coincide.  (Contributed
       by Stefan O'Rear, 8-Nov-2014.) $)
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
       between strict orders.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
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

  $( Strict dominance and elementhood are the same for finite ordinals.
     (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
  nnsdomel $p |- ( ( A e. om /\ B e. om ) -> ( A e. B <-> A ~< B ) ) $=
    ( com wcel wa ccrd cfv csdm wbr wceq wb cardnn eleq12 syl2an cfn cin onfin2
    con0 inss2 sseli eqsstri ficardsdom bitr3d ) ACDZBCDZEAFGZBFGZDZABDZABHIZUD
    UFAJUGBJUHUIKUEALBLUFAUGBMNUDAODBODUHUJKUECOACROPOQROSUAZTCOBUKTABUBNUC $.
    $( [2-Nov-2014] $)

  $( An ordinal with more elements of some type is larger.  (Contributed by
     Stefan O'Rear, 2-Nov-2014.) $)
  onsdominel $p |- ( ( A e. On /\ B e. On /\ ( A i^i C ) ~< ( B i^i C ) ) ->
      A e. B ) $=
    ( con0 wcel cin csdm wbr wa wn wb ontri1 ancoms wi cdom inex1g ssrin ssdomg
    wss cvv syl2im domnsym syl6 adantl sylbird con4d 3impia ) ADEZBDEZACFZBCFZG
    HZABEZUHUIIZUMULUNUMJZBASZULJZUIUHUPUOKBALMUIUPUQNUHUIUPUKUJOHZUQUIUKTEUPUK
    UJSURBCDPBACQUKUJTRUAUKUJUBUCUDUEUFUG $.
    $( [2-Nov-2014] $)

  ${
    $d F a $.  $d X a $.

    $( Two possibilities for the behavior of a function value.  (Contributed by
       Stefan O'Rear, 2-Nov-2014.) $)
    fvbr0 $p |- ( X F ( F ` X ) \/ ( F ` X ) = (/) ) $=
      ( va cv csn cima wcel weu cfv wbr c0 wceq wo cio wsbc iota4 eqcomi dfsbcq
      wb dffv3 ax-mp fvex eleq1 sbcie bitri biimpi elimasni 3syl orcd wn syl5eq
      iotanul olcd pm2.61i ) CDZABEFZGZCHZBBAIZAJZUSKLZMURUTVAURUQCUQCNZOZUSUPG
      ZUTUQCPVCVDVCUQCUSOZVDVBUSLVCVESUSVBCBATZQUQCVBUSRUAUQVDCUSBAUBUOUSUPUCUD
      UEUFABUSUGUHUIURUJZVAUTVGUSVBKVFUQCULUKUMUN $.
      $( [2-Nov-2014] $)

    $( The result of a function value is always a subset of the union of the
       range, even if it is invalid and thus empty.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
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
    $( A subset of a III-finite set is III-finite.  (Contributed by Stefan
       O'Rear, 4-Nov-2014.) $)
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
    $( The beginning of the proof that every II-finite set (every chain of
       subsets has a maximal element) is III-finite (has no denumerable
       collection of subsets).

       This first section is sedicated to the construction of ` U ` and its
       intersection.  First, the value of ` U ` at a successor. $)
    fin23lem12 $p |- ( A e. om -> ( U ` suc A ) = if ( ( ( t ` A ) i^i
        ( U ` A ) ) = (/) , ( U ` A ) , ( ( t ` A ) i^i ( U ` A ) ) ) ) $=
      ( com wcel csuc cfv cvv cv cin c0 wceq cif cmpt2 co crn eqeq1d cuni fveq2
      seqomsuc fvex ineq1d ifbieq2d ineq2 id1 ifbieq12d eqid inex2 ovmpt2 mpan2
      ifex eqtrd ) CGHZCIDJCCDJZEAGKELZBLZJZALZMZNOZVAVBPZQZRZCUSJZUQMZNOZUQVHP
      ZCVEDUSSUAFUCUPUQKHVFVJOCDUDZEACUQGKVDVJVEVGVAMZNOZVAVLPURCOZVCVMVBVLVAVN
      VBVLNVNUTVGVAURCUSUBUEZTVOUFVAUQOZVMVIVAVLUQVHVPVLVHNVAUQVGUGZTVPUHVQUIVE
      UJVIUQVHVKUQVGVKUKUNULUMUO $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 .  Each step of ` U ` is a decrease. $)
    fin23lem13 $p |- ( A e. om -> ( U ` suc A ) C_ ( U ` A ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq cif fin23lem12 wss sseq1 ssid inss2
      keephyp a1i eqsstrd ) CGHZCIDJCBKJZCDJZLZMNZUFUGOZUFABCDEFPUIUFQZUDUHUFUF
      QUGUFQUJUFUGUFUIUFRUGUIUFRUFSUEUFTUAUBUC $.
      $( [1-Nov-2014] $)

    $( Lemma for ~ fin23 . ` U ` will never evolve to an empty set if it did
       not start with one. $)
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
      a1i wi ad2antrr sstr2 syl findsg ) HJZEKZDEKZLUKUKLZIJZEKZUKLZUMMZEKZUKLZ
      CEKZUKLHICDUIDNUJUKUKUIDEOPHIQUJUNUKUIUMEOPUIUPNUJUQUKUIUPEOPUICNUJUSUKUI
      CEOPULDRSZUKUAUCUMRSZUTTDUMLZTUQUNLZUOURUDVAVCUTVBABUMEFGUBUEUQUNUKUFUGUH
      $.
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
      a1i inteqd cla4gv syl3c syl2an ) BIZJZUAZUBKZLWTMZFIZNZGIZUDZXCOZXEXCOZPZ
      GLUEZQZXCJZUFZXLKZRZFUCZLSKZCJZUFZXRKZLSWRUGZXAXPLHIZMZXCNZXJQZXNRZFUCXPH
      WTUBWSWRBUQZUHUIYBWTTZYFXOFYHYEXKXNYHYDXDXJYHYCXBTYDXDUJYBWTUKYCXBLXCULUR
      UMUNUOHFGUPUSUTYAWRSKLSWRNXQYGLSWRVALSSWRVBVCXPXQQZCSKZXPLXBCNZXFCOZXECOZ
      PZGLUEZQZXTXQYJXPCLVDZXQYJDALSDIWROAIZVEZVFTYRYSVKVGCWTEVHZLSCVIVJVLXPXQV
      MYPYIYKYOLXRCNZXRXBPYKYQUUAYTLCVNVOXRXRUAZMXBXRVPUUBWTABCDEVQVRVSLXRXBCVT
      WBYNGLABXECDEWAWCWDWMXOYPXTRFCSXCCTZXKYPXNXTUUCXDYKXJYOLXBXCCWEUUCXIYNGLU
      UCXGYLXHYMXFXCCWFXEXCCWFWGWHWIUUCXMXSXLXRUUCXLXRXCCWJZWNUUDWKWLWOWPWQ $.
      $( [4-Nov-2014] $)

    $( Lemma for ~ fin23 .  The first set in ` U ` to see an input set is
       either contained in it or disjoint from it. $)
    fin23lem19 $p |- ( A e. om -> ( ( U ` suc A ) C_ ( t ` A ) \/
      ( ( U ` suc A ) i^i ( t ` A ) ) = (/) ) ) $=
      ( com wcel csuc cfv cv cin c0 wceq wss cif wa wn wo fin23lem12 eqif incom
      biimpi ineq2 eqeq1d biimparc syl5eq inss1 sseq1 mpbiri adantl 3syl orcomd
      orim12i ) CGHZCIDJZCBKJZLZMNZUPUQOZUOUPUQCDJZLZMNZVAVBPNZVCUPVANZQZVCRZUP
      VBNZQZSZUSUTSABCDEFTVDVJVCUPVAVBUAUCVFUSVIUTVFURUQUPLZMUPUQUBVEVKMNVCVEVK
      VBMUPVAUQUDUEUFUGVHUTVGVHUTVBUQOUQVAUHUPVBUQUIUJUKUNULUM $.
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
      ccom eqeq1d ifbieq2d ineq2 id ifbieq12d cbvmpt2v seqomeq12 sseq2d cbvrabv
      mp2an fin23lem32 ) DEFGHUAIJMUBINZUANZOZJNZPZQRZVNVOSZUCZVLUDUEZUFZUDUGZK
      NZVLOZUHZKMUIZFMDNZWEPFNZUJUKDWEUIUEULZFMWFMWEUMZPWGUJUKDWIUIUEULZVTLAWEU
      NUOVLWJUSEWEENVLOWAUMULWHUSSZBCVRLHMUBLNZVLOZHNZPZQRZWNWOSZUCZRVSVSRVTWRV
      SUFRIJLHMUBVQWQWMVNPZQRZVNWSSILUPZVPWTVOWSVNXAVOWSQXAVMWMVNVKWLVLUQURZUTX
      BVAJHUPZWTWPVNWSWNWOXCWSWOQVNWNWMVBZUTXCVCXDVDVEVSTVRWRVSVSVFVIWDWAGNZVLO
      ZUHKGMKGUPWCXFWAWBXEVLUQVGVHWHTWJTWKTVJ $.
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
      wceq imbi2d ssid a1i12 wpss simprr simpll fin23lem35 syl2anc pssssd sstr2
      weq syl expr a2d findsg impr ) BUCUDCUCUDZMCBNABHOZPZQZCHOZPZQZNZAUAUEZHO
      ZPZQZVLNZRAVLVLNZRAUBUEZHOZPZQZVLNZRAVTUFZHOZPZQZVLNZRAVMRUAUBBCVNCUIZVRV
      SAWJVQVLVLWJVPVKWJVOVJVNCHSTUGUHUJUAUBUTZVRWDAWKVQWCVLWKVPWBWKVOWAVNVTHST
      UGUHUJVNWEUIZVRWIAWLVQWHVLWLVPWGWLVOWFVNWEHSTUGUHUJVNBUIZVRVMAWMVQVIVLWMV
      PVHWMVOVGVNBHSTUGUHUJVFAVSVLUKULVTUCUDZVFMZCVTNZMAWDWIWOWPAWDWIRZWOWPAMZM
      ZWHWCNWQWSWHWCWSAWNWHWCUMWOWPAUNWNVFWRUOAVTDEFGHIJKLUPUQURWHWCVLUSVAVBVCV
      DVE $.
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
      ( vb vc ve vd cv wcel cfv crn com cvv cuni wceq wrex cint fin23lem38 cmpt
      cfin2ds cab cpw wf csuc wss wral wi wf1 vex f1f dmfex sylancr mptexg 3syl
      wa fin23lem34 simprd elpw2 sylibr fmptd fin23lem35 pssssd wb peano2 fveq2
      eqid rneqd unieqd fvex rnex uniex syl weq sseq12d adantl mpbird ralrimiva
      fvmpt wal df-fin2ds abeq2i feq1 fveq1 ralbidv anbi12d rneq inteqd eleq12d
      imbi12d cla4gv syl5bi com23 imp syl12anc rnmpt inteqi eleq12i syl6ib mtod
      ) ABOZUGPZKOLOZFQZRZUAZUBLSUCKUHZUDZXMPZABCDEFKLGHIJUEAXHLSXLUFZRZUDZXQPZ
      XOAXPTPZSXGUIZXPUJZMOZUKZXPQZYCXPQZULZMSUMZXHXSUNZASTCOZUOZSTPZXTGYKYJTPS
      TYJUJYLCUPSTYJUQSTTYJURUSLSXLTUTVAALSXLYAXPAXISPVBZXLXGULZXLYAPYMSTXJUOYN
      AXIBCDEFGHIJVCVDXLXGBUPVEVFXPVMZVGAYGMSAYCSPZVBZYGYDFQZRZUAZYCFQZRZUAZULZ
      YQYTUUCAYCBCDEFGHIJVHVIYPYGUUDVJAYPYEYTYFUUCYPYDSPYEYTUBYCVKLYDXLYTSXPXIY
      DUBZXKYSUUEXJYRXIYDFVLVNVOYOYSYRYDFVPVQVRWEVSLYCXLUUCSXPLMVTZXKUUBUUFXJUU
      AXIYCFVLVNVOYOUUBUUAYCFVPVQVRWEWAWBWCWDXTYBYHVBZYIXTXHUUGXSXHSYANOZUJZYDU
      UHQZYCUUHQZULZMSUMZVBZUUHRZUDZUUOPZUNZNWFZXTUUGXSUNZUUSBUGBNMWGWHUURUUTNX
      PTUUHXPUBZUUNUUGUUQXSUVAUUIYBUUMYHSYAUUHXPWIUVAUULYGMSUVAUUJYEUUKYFYDUUHX
      PWJYCUUHXPWJWAWKWLUVAUUPXRUUOXQUVAUUOXQUUHXPWMZWNUVBWOWPWQWRWSWTXAXRXNXQX
      MXQXMLKSXLXPYOXBZXCUVCXDXEXF $.
      $( [4-Nov-2014] $)
  $}

  ${
    $d a b x $.
    $( Alternate definition of IV-finite sets: they lack a denumerable subset.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
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
       ordinal.  (Contributed by Stefan O'Rear, 5-Nov-2014.) $)
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
      nnord sseld elndif syl56 ralrimiv disj sylibr ) CKLZDKLZMZDCLZAMZMZJNZDEN
      ZOZDPZVJOZQZLRZJCVJOZCPVJOZQZSVRVNUAUBUFVHVOJVRVIVRLVIVPLVHVIVMLVOVIVPVQU
      CVHVPVMVIVHVCVLKLZVLCTZAVPVMTVCVDVGUDVDVSVCVGDUEUGVHCUHZVFVTVCWAVDVGCUPUI
      VEVFAUJDCUKULVEVFAUMABCVLEFGHIUNUOUQVIVMVKURUSUTJVRVNVAVB $.
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
      ( cv com wfo wex df32lem9 cvv wcel wf fof vex sylancl foeq1 cla4egv mpcom
      fex syl ) AJUCZUDMUEZUSUDOUCZUEZOUFZABCDEFGHIJKLMNPQRSTUAUBUGMUHUIZUTVCUT
      USUDMUJUSUHUIVDUSUDMUKJULUSUDUHMUQUMVBUTOMUHUSUDVAMUNUOUPUR $.
      $( [6-Nov-2014] $)
  $}

  ${
    $d A x y a b $.  $d F a b y $.  $d G a b x y $.
    compssiso.a $e |- F = ( x e. ~P A |-> ( A \ x ) ) $.
    compssiso.b $e |- A e. _V $.
    $( Complementation is an antiautomorphism on power set latticies.
       (Contributed by Stefan O'Rear, 4-Nov-2014.) $)
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

    $( Express image under of the complementation isomorphism.  (Contributed by
       Stefan O'Rear, 5-Nov-2014.) $)
    compss $p |- ( G C_ ~P A -> ( F " G ) = { y e. ~P A | ( A \ y ) e. G } ) $=
      ( va vb wss cv cdif wcel wceq wrex wa wb difeq2 cvv elpw2 cima crab ssel2
      cpw cfv difexg ax-mp fvmpt syl rexbidva difss mpbir eleq1 mpbii rexlimivw
      eqeq1d pm4.71ri dfss4 bitri sylib eqcomd eqeq2d syl5ibcom biimpi ad2antlr
      adantlr syl5ibrcom impbid risset syl6bbr pm5.32da syl5bb bitrd fnmpt mprg
      wfn a1i fvelimab mpan weq eleq1d elrab 3bitr4d eqrdv ) ECUDZJZHDEUAZCBKZL
      ZEMZBWEUBZWFIKZDUEZHKZNZIEOZWNWEMZCWNLZEMZPZWNWGMZWNWKMZWFWPCWLLZWNNZIEOZ
      WTWFWOXDIEWFWLEMZPZWLWEMZWOXDQEWEWLUCZXHWMXCWNAWLCAKZLZXCWEDXJWLCRFCSMZXC
      SMGCWLSUFUGUHUPUIUJXEWQXEPWFWTXEWQXDWQIEXDXCWEMZWQXMXCCJCWLUKXCCGTULXCWNW
      EUMUNUOUQWFWQXEWSWFWQPZXEWLWRNZIEOWSXNXDXOIEXNXFPZXDXOXPWLCXCLZNXDXOXPXQW
      LWFXFXQWLNZWQXGXHXRXIXHWLCJXRWLCGTWLCURUSUTVFVAXDXQWRWLXCWNCRVBVCXPXDXOCW
      RLZWNNZWQXTWFXFWQXTWQWNCJXTWNCGTWNCURUSVDVEXOXCXSWNWLWRCRUPVGVHUJIWREVIVJ
      VKVLVMDWEVPZWFXAWPQXKSMZYAAWEAWEXKDSFVNYBXJWEMXLYBGCXJSUFUGVQVOIWEEWNDVRV
      SXBWTQWFWJWSBWNWEBHVTWIWREWHWNCRWAWBVQWCWD $.
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
      ( va vb vc vd vh vg vf vk ve vl cv wcel com csuc cfv wn cmpt eqid cfin2ds
      cpw wf wss wral wa crn cint wal wfo wex df-fin2ds abeq2i exnal annim wpss
      wi crab cin cen wbr cuni cdif ccom wreu crio c0 simpll suceq fveq2d fveq2
      cif weq sseq12d cbvralv biimpi ad2antlr psseq12d cbvrabv df32lem10 sylbir
      simpr exlimiv sylnbi ) BMZUANOWEUBCMZUCZDMZPZWFQZWHWFQZUDZDOUEZUFZWFUGZUH
      WONZUQZCUIZWEOAMUJAUKZWRBUABCDULUMWRRWQRZCUKWSWQCUNWTWSCWTWNWPRZUFZWSWNWP
      UOXBEFGHIJKMZPZWFQZXCWFQZUPZKOURZCBIOHMXHUSIMUTVAHXHURVBSZGXHGMZWFQXJPWFQ
      VCSXIVDZJWEJMLMXKQNZLOVEXLLOVFVGVLSZLAWGWMXAVHWMEMZPZWFQZXNWFQZUDZEOUEZWG
      XAWMXSWLXRDEODEVMZWJXPWKXQXTWIXOWFWHXNVIVJWHXNWFVKVNVOVPVQWNXAWBXGFMZPZWF
      QZYAWFQZUPKFOKFVMZXEYCXFYDYEXDYBWFXCYAVIVJXCYAWFVKVRVSXITXKTXMTVTWAWCWAWD
      $.
      $( [6-Nov-2014] $)

    $( Weakly Dedekind-infinite sets are exactly those which can be mapped onto
       ` om ` .  (Contributed by Stefan O'Rear, 6-Nov-2014.) $)
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
       descending chain of subsets.  (Contributed by Stefan O'Rear,
       7-Nov-2014.) $)
    dffin3-3 $p |- Fin3 = { g | A. a ( ( a : om --> ~P g /\
        A. b e. om ( a ` suc b ) C_ ( a ` b ) ) -> |^| ran a e. ran a ) } $=
      ( cfin3 cfin2ds com cv cpw wf csuc cfv wss wral wa crn cint wcel wi wal
      wn cab wfo df32lem12 dffin3-2 abeq2i con2bii sylib con4i ssriv fin23lem41
      wex eqssi df-fin2ds eqtri ) DEFAGHBGZICGZJUOKUPUOKLCFMNUOOZPUQQRBSAUADEBD
      EUOEQZUODQZURTUOFUPUBCUKZUSTCBUCUSUTUTTBDBCUDUEUFUGUHUIUJULABCUMUN $.
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
       ascending chain of subsets.  (Contributed by Stefan O'Rear,
       7-Nov-2014.) $)
    dffin3-4 $p |- Fin3 = { g | A. a ( ( a : om --> ~P g /\
        A. b e. om ( a ` b ) C_ ( a ` suc b ) ) -> U. ran a e. ran a ) } $=
      ( vc cv cpw cdif cmpt eqid dff34lem6 ) DADAEZFKDEGHZBCLIJ $.
      $( [7-Nov-2014] $)

  $}

  ${
    $d H a b c $.  $d R a b c $.  $d S a b c $.  $d K a b c $.  $d A a b c $.
    $d B a b c $.  $d X a b c $.
    $( Induced isomorphism on a subset.  (Contributed by Stefan O'Rear,
       5-Nov-2014.) $)
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

    $( Every I-finite set is Ia-finite.  (Contributed by Stefan O'Rear,
       30-Oct-2014.) $)
    fin11a $p |- Fin C_ Fin1a $=
      ( va vb vc cfn cfin1a cv wcel cun wceq cin c0 wa wn wex unfir con3i eleq1
      simpld notbid syl5ibr imp ad2ant2r exlimivv con2i df-fin1a abeq2i sylibr
      ssriv ) ADEAFZDGZUIBFZCFZHZIZUKULJKIZLUKDGZMZULDGZMZLLZCNBNZMZUIEGVAUJUTU
      JMZBCUNUQVCUOUSUNUQVCUQVCUNUMDGZMVDUPVDUPURUKULORPUNUJVDUIUMDQSTUAUBUCUDV
      BAEABCUEUFUGUH $.
      $( [30-Oct-2014] $)

    $( A set is finite in the usual sense iff the power set of its power set is
       Dedekind finite.  This provides an alternate proof of ~ fineqv .
       (Contributed by Stefan O'Rear, 3-Nov-2014.) $)
    dffin1-2 $p |- Fin = { x | ~P ~P x e. Fin4 } $=
      ( va vb vc vd ve cfn cv cpw cfin4 wcel com cdom wbr wn cen wa syl wi ex
      cab vex pwex wceq breq2 notbid dffin4-2 elab2 pweq pweqd eleq1d elab pwfi
      weq bitri isfinite1 sbth expcom con3d imp sylbi con2i cvv crab wss ssrab2
      elpw2 mpbir a1i12 wb wex wral isinf ra4 adantrd anim1i breq1 elrab sylibr
      biimpri eximi eleq2 biimpcd adantl simprbi ensym entr sylan syl2an nneneq
      biimpd ad2antlr 3syld exlimdv mpd rabbidv impbid1 impbii con2bii 3bitr4ri
      dom3d mpi eqriv ) BGAHZIZIZJKZAUAZBHZIZIZJKZLXKMNZOZXIXHKXIGKZLCHZMNZOXNC
      XKJXJXIBUBZUCZUCZXPXKUDXQXMXPXKLMUEUFCUGUHXGXLAXIXRABUNZXFXKJYAXEXJXDXIUI
      UJUKULXMXOXMXOOZXOXMXOXKGKZXNXOXJGKYCXIUMXJUMUOYCXKLMNZLXKPNZOZQXNXKUPYDY
      FXNYDXMYEXMYDYELXKUQURUSUTRVAVBYBXKVCKXMXTYBCDLXKEHZXPPNZEXJVDZYGDHZPNZEX
      JVDZVCYBXPLKZYIXKKZYNYIXJVEYHEXJVFYIXJXSVGVHVIYBYMYJLKZQZYIYLUDZCDUNZVJYB
      YPQZYQYRYSFHZYIKZFVKZYQYRSZYSYTXIVEZYTXPPNZQZFVKZUUBYBYPUUGYBYMUUGYOYBUUG
      CLVLYMUUGSFXICVMUUGCLVNRVOUTUUFUUAFUUFYTXJKZUUEQUUAUUDUUHUUEUUHUUDYTXIXRV
      GVTVPYHUUEEYTXJYGYTXPPVQVRZVSWARYSUUAUUCFYSUUAUUCYSUUAQYQYTYLKZXPYJPNZYRU
      UAYQUUJSYSYQUUAUUJYIYLYTWBWCWDUUAUUJUUKSYSUUAUUJUUKUUAUUEYTYJPNZUUKUUJUUA
      UUHUUEUUIWEUUJUUHUULYKUULEYTXJYGYTYJPVQVRWEUUEXPYTPNUULUUKYTXPCUBWFXPYTYJ
      WGWHWITWDYPUUKYRSYBUUAYPUUKYRXPYJWJWKWLWMTWNWOYRYHYKEXJXPYJYGPUEWPWQTXAXB
      WRWSWTXC $.
      $( [3-Nov-2014] $)

    $( A set is I-finite iff every system of subsets contains a maximal
       subset.  Definition I of [Levy] p. 2.  (Contributed by Stefan O'Rear,
       4-Nov-2014.) $)
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
       subset.  (Contributed by Stefan O'Rear, 4-Nov-2014.) $)
    dffin1-4 $p |- Fin = { x | {C.} Fr ~P x } $=
      ( va vb cfn cpw crpss wfr cab ccnv wcel cdif cmpt wiso eqid vex compssiso
      cv wb isofr ax-mp weq wceq pweq freq2 elab dffin1-3 abeq2i 3bitr4ri eqriv
      syl ) BDAQZEZFGZAHZBQZEZFGZUPFIZGZUOUNJUODJUPUPFURCUPUOCQKLZMUQUSRCUOUTUT
      NBOZPUPUPFURUTSTUMUQAUOVAABUAULUPUBUMUQRUKUOUCULUPFUDUJUEUSBDBUFUGUHUI $.
      $( [4-Nov-2014] $)

    $( Every II-finite set (every chain of subsets has a maximal element) is
       III-finite (has no denumerable collection of subsets).  The proof here
       is the only one I could find, from
       ~ http://matwbn.icm.edu.pl/ksiazki/fm/fm6/fm619.pdf p.94 (writeup by
       Tarski, credited to Kuratowski).  Translated into English and modern
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
       contradicting the first assumption.  (Contributed by Stefan O'Rear,
       2-Nov-2014.) $)
    fin23 $p |- Fin2 C_ Fin3 $=
      ( cfin2 cfin2ds cfin3 fin23lem40 fin23lem41 sstri ) ABCDEF $.
      $( [2-Nov-2014] $)

    $( Every III-finite set is IV-finite.  (Contributed by Stefan O'Rear,
       30-Oct-2014.) $)
    fin34 $p |- Fin3 C_ Fin4 $=
      ( va vb cfin3 cfin4 cv cpw wcel com cdom wbr vex pwex wceq breq2 dffin4-2
      wn notbid elab2 csdm abeq2i domsdomtr mpan2 sdomdom con3i df-fin3 3imtr4i
      canth2 syl sylbi ssriv ) ACDAEZFZDGZHUKIJZPZUKCGUKDGUMHULIJZPZUOHBEZIJZPU
      QBULDUKAKZLURULMUSUPURULHINQBORUNUPUNHULSJZUPUNUKULSJVAUKUTUGHUKULUAUBHUL
      UCUHUDUIUMACAUETUOADAOTUFUJ $.
      $( [30-Oct-2014] $)

    $( Alternate definition of V-finite which emphasizes the idempotent
       behavior of V-infinite sets.  (Contributed by Stefan O'Rear,
       30-Oct-2014.) $)
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
       into itself, we can certainly leave space.  (Contributed by Stefan
       O'Rear, 30-Oct-2014.) $)
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
       addition for cardinals.  (Contributed by Stefan O'Rear, 29-Oct-2014.) $)
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
       like the others, if there is interest.  (Contributed by Stefan O'Rear,
       29-Oct-2014.) $)
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
       "weakest" and the entire hierarchy collapses.  (Contributed by Stefan
       O'Rear, 29-Oct-2014.) $)
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
      ( va con0 wcel csuc cfv wceq suceloni cv suceq cbvmptv eqtri fvmptg mpdan
      cmpt ) BFGBHZFGBCISJBKEBELZHZSFFCTBMCAFALZHZREFUARDAEFUCUAUBTMNOPQ $.
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
      syl mpcom jca notbid anbi12d syl5ibcom rexlimiv wne c2o peano1 fin1a2lem3
      comu co om0x eqtri wfun cdm f1dm eleqtrri fvelrn eqeltrri mpbiri necon3bi
      f1fun nnsuc sylan2 anbi1d simplr adantl mpbird syl6bi com12 simprr eqcomd
      impr ex reximdv2 mpd impbii bitri wfn fvelimab eldif 3bitr4i eqriv f1oeq3
      f1fn mpbi ) CUCZBXNUDZBXNUEZHZXNIXNUFZXPHZJJBKZXNJUGZXQABEUHZIICKZIICUAZY
      AACDUIZIICUJZYDXNIJIICUKZULUMUOZJJXNBUNLXOXRMXQXSNFXOXRGUBZBUPZFUBZMZGXNO
      ZYKIPZYKXNPZUQZQZYKXOPZYKXRPYMYIURZYKMZGXNOZYQYLYTGXNYIXNPZYJYSYKUUBYIJPY
      JYSMXNJYIYHUSAYIBEUTVFVAVBUUAYQYTYQGXNUUBYSIPZYSXNPZUQZQZYTYQUUBUUCUUEUUB
      YIIPZUUCXNIYIYCYDXNIUGYEYFYGUOUSZYIVCVFUUGUUBUUEUUHUUGUUBUUEAYICDVDZVEVGV
      HYTUUCYNUUEYPYSYKIRYTUUDYOYSYKXNRVIVJVKVLYQYKYSMZGIOZUUAYPYNYKSVMUUKYOYKS
      YKSMYOSXNPSCUPZSXNUULVNSVQVRZSSIPUULUUMMVOASCDVPTVNVSVTCWAZSCWBZPUULXNPYC
      UUNYEIICWITSIUUOVOYCUUOIMYEIICWCTWDSCWELWFYKSXNRWGWHGYKWJWKYQUUJYTGIXNYQU
      UGUUJQZUUBYTQYQUUPQZUUBYTYQUUGUUJUUBUUJYQUUGQZUUBUUJUURUUFUUGQZUUBUUJYQUU
      FUUGUUJYNUUCYPUUEYKYSIRUUJYOUUDYKYSXNRVIVJWLUUSUUBUUEUUCUUEUUGWMUUGUUBUUE
      NUUFUUIWNWOWPWQWTUUQYKYSYQUUGUUJWRWSVHXAXBXCXDXEBJXFZYAYRYMNXTUUTYBJJBXLT
      YHGJXNYKBXGLYKIXNXHXIXJXOXRXNXPXKTXM $.
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
      UWPYDUPVWDVWBDUWEUWPUVRUWEMSYEYFUVEUVMXTTYGBUVDUVMYHTUVOUVMUVIQVUHVVNUVMU
      VDXCXPYIUVOVUHVVNYMYJYKYFYLVUTUVHVUNUVOVVOUVQUVHVUOVUSUYGXPUVQVUNVUHVUSYN
      VVPUVDUXFUVMWEYOVVNVVMYPYQUVMUXFYRUPYSVUQVVKQVVLVURVUQUVMYTVUQVVKUXFUUAUU
      BUUEUUCUUDYGHUVDUXFYHTVUNUXFUVIQUVQVUHUXFUVDXCUUFYIUVQVUNVUHUUGYJWKVCWIYL
      UUHUWTUXBUUIUPUWIUXDDUWPUWGUVRUWPPZUWDUXCVWKUWAUWTUWCUXBVWKUVSUWRUVTUWSUV
      RUWPMUUJUVRUWPUBUUKUULVWKUWBUXAUVRUWPUVRUWPUUPVWKUUMUUNUUOUUQVPYFUWDDUWGU
      URUPUWDDUWKUAZUAZNUWHEUWEUJUXTVWIUWDDVWMUWGVWIVWLUWFUWKUWEUUSUUTUVAEDUVBW
      SUVC $.
      $( [8-Nov-2014] $)

    $( Weak theorem which skips Ia but has a trivial proof, needed to prove
       ~ fin1a2 .  (Contributed by Stefan O'Rear, 8-Nov-2014.) $)
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
       II-infinite.  (Contributed by Stefan O'Rear, 8-Nov-2014.) $)
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

    $( Every Ia-finite set is II-finite.  Theorem 1 of [Levy], p. 3.
       (Contributed by Stefan O'Rear, 8-Nov-2014.) $)
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
    Unsorted preliminaries for Liouville's approximation theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d F a $.
    $( Real-coefficient polynomials restrict to real functions. $)
    plyreres $p |- ( F e. ( Poly ` RR ) -> ( F |` RR ) : RR --> RR ) $=
      ( va cr cply cfv wcel cres wfn crn wss wf cc plybss wb plyf mpbird adantl
      ffn wceq ccj fnssresb 3syl cv wral fvres recn plyrecj sylan2 fveq2d eqtrd
      cjre ffvelrn syl2an cjreb syl eqeltrd ralrimiva fnfvrnss syl2anc sylanbrc
      wa df-f ) ACDEFZACGZCHZVDICJZCCVDKVCVECLJZCAMVCLLAKZALHVEVGNCAOZLLARLCAUA
      UBPZVCVEBUCZVDEZCFZBCUDVFVJVCVMBCVCVKCFZVAZVLVKAEZCVNVLVPSVCVKCAUEQVOVPCF
      ZVPTEZVPSZVOVRVKTEZAEZVPVNVCVKLFZVRWASVKUFZVKAUGUHVOVTVKAVNVTVKSVCVKUKQUI
      UJVOVPLFZVQVSNVCVHWBWDVNVIWCLLVKAULUMVPUNUOPUPUQBCCVDURUSCCVDVBUT $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d ph i x a b c d $.  $d X i x a b c d $.  $d I i x a b c d $.
    $d A a b c d $.  $d B a b c d $.
    dvmptfsum.x $e |- ( ph -> X C_ RR ) $.
    dvmptfsum.i $e |- ( ph -> I e. Fin ) $.
    dvmptfsum.a $e |- ( ( ph /\ i e. I /\ x e. X ) -> A e. CC ) $.
    dvmptfsum.b $e |- ( ( ph /\ i e. I /\ x e. X ) -> B e. CC ) $.
    dvmptfsum.d $e |- ( ( ph /\ i e. I ) -> ( _D ` ( x e. X |-> A ) ) =
        ( x e. X |-> B ) ) $.
    dvmptfsum.o $e |- ( ph -> X e. ( topGen ` ran (,) ) ) $.
    $( Function-builder for derivative, finite sums rule. $)
    dvmptfsum $p |- ( ph -> ( _D ` ( x e. X |-> sum_ i e. I A ) ) =
        ( x e. X |-> sum_ i e. I B ) ) $=
      ( va vd cmpt cdv wceq wcel wi vb vc wss csu cfv ssid cfn cv csn cun sseq1
      c0 sumeq1 mpteq2dv fveq2d eqeq12d imbi12d imbi2d weq cc0 cc cr a1i wa 0cn
      dvmptc dvmptres sum0 mpteq2i fveq2i 3eqtr4g a1d wn ssun1 sstr mpan imim1i
      wel csb caddc cvv ad2antrr ad3antrrr ad2antlr ssfi syl2anc simp1ll sselda
      3expa simplr w3a ax-17 vex ax17el hbcsb1 hbel hbim 3anbi3d csbeq1a eleq1d
      eleq1 chvar syl3anc fsumcl adantlrr sumex sumeq2sdv cbvmpt eqeq12i biimpi
      co hbsum ad2antll simplll ssun2 snss sylibr simpr wral ancom2s ralrimivva
      3expb rcla42 ancoms mpan9 syl12anc simpll hbmpt csbeq2dv fsumsplit sumsns
      hbcsb mpan2 sylancr oveq2d eqtrd mpteq2dva syl5eq adantrr a2d hbfv anbi2d
      ad2antrl hbeq 3eqtr3g dvmptadd cin simpllr disjsn eqidd exp32 syl5 expcom
      3eqtr4d adantl findcard2s mpcom mpi ) AFFUCZBGFCEUDZPZQUEZBGFDEUDZPZRZFUF
      FUGSZAUUSUVETZIANUHZFUCZBGUVHCEUDZPZQUEZBGUVHDEUDZPZRZTZTAULFUCZBGULCEUDZ
      PZQUEZBGULDEUDZPZRZTZTAUAUHZFUCZBGUWECEUDZPZQUEZBGUWEDEUDZPZRZTZTAUWEUBUH
      ZUIZUJZFUCZBGUWPCEUDZPZQUEZBGUWPDEUDZPZRZTZTAUVGTNUAUBFUVHULRZUVPUWDAUXEU
      VIUVQUVOUWCUVHULFUKUXEUVLUVTUVNUWBUXEUVKUVSQUXEBGUVJUVRUVHULCEUMUNUOUXEBG
      UVMUWAUVHULDEUMUNUPUQURNUAUSZUVPUWMAUXFUVIUWFUVOUWLUVHUWEFUKUXFUVLUWIUVNU
      WKUXFUVKUWHQUXFBGUVJUWGUVHUWECEUMUNUOUXFBGUVMUWJUVHUWEDEUMUNUPUQURUVHUWPR
      ZUVPUXDAUXGUVIUWQUVOUXCUVHUWPFUKUXGUVLUWTUVNUXBUXGUVKUWSQUXGBGUVJUWRUVHUW
      PCEUMUNUOUXGBGUVMUXAUVHUWPDEUMUNUPUQURUVHFRZUVPUVGAUXHUVIUUSUVOUVEUVHFFUK
      UXHUVLUVBUVNUVDUXHUVKUVAQUXHBGUVJUUTUVHFCEUMUNUOUXHBGUVMUVCUVHFDEUMUNUPUQ
      URAUWCUVQABGUTPZQUEUXIUVTUWBABUTUTVAVBGVBVBUCAVBUFVCUTVASZABUHZVBSVDVEVCZ
      UXLABUTUXJAVEVCVFHMVGUVSUXIQBGUVRUTCEVHVIVJBGUWAUTDEVHVIVKVLUWEUGSZUBUAVR
      VMZVDAUWMUXDUXNAUWMUXDTZTUXMAUXNUXOUWMUWQUWLTAUXNVDZUXDUWQUWFUWLUWEUWPUCU
      WQUWFUWEUWOVNUWEUWPFVOVPZVQUXPUWQUWLUXCUXPUWQUWLUXCUXPUWQUWLVDZVDZNGUWEBU
      VHCVSZEUDZEUWNUXTVSZVTXKZPZQUENGUWEBUVHDVSZEUDZEUWNUYEVSZVTXKZPZUWTUXBUXS
      NUYAUYFUYBUYGWAVAGAGVBUCUXNUXRHWBUXPUWQUVHGSZUYAVASUWLUXPUWQVDZUYJVDZUWEU
      XTEUYLUVFUWFUXMAUVFUXNUWQUYJIWCZUWQUWFUXPUYJUXQWDZFUWEWEWFUYLEUAVRZVDAEUH
      ZFSZUYJUXTVASZUYKUYJUYOAAUXNUWQUYJUYOWGWIUYLUWEFUYPUYNWHUYKUYJUYOWJAUYQUX
      KGSZWKZCVASZTAUYQUYJWKZUYRTBNVUBUYRBVUBBWLZBOOUXTVABOUVHCNWMZONBWNZWOZOUH
      ZVASZBWLZWPZWQBNUSZUYTVUBVUAUYRVUKUYSUYJAUYQUXKUVHGXAWRZVUKCUXTVABUVHCWSZ
      WTZUQJXBZXCXDXEUYFWASUXSUYJVDUWEUYEEXFVCUWLNGUYAPZQUEZNGUYFPZRZUXPUWQUWLV
      USUWIVUQUWKVURUWHVUPQBNOGUWGUYAVUGUWGSNWLBOUWEUXTEOUABWNZVUFXLVUKUWECUXTE
      VUMXGXHVJBNOGUWJUYFVUGUWJSNWLBOUWEUYEEVUTBOUVHDVUDVUEWOZXLVUKUWEDUYEEBUVH
      DWSZXGXHXIXJXMUXPUWQUYJUYBVASZUWLUYLAUWNFSZUYJVVCAUXNUWQUYJXNZUWQVVDUXPUY
      JUWQUWOFUCZVVDUWOUWPUCUWQVVFUWOUWEXOUWOUWPFVOVPUWNFUBWMZXPXQZWDZUYKUYJXRZ
      AVUAEFXSBGXSZVVDUYJVDZVVCAVUABEGFAUYQUYSVUAAUYQUYSVUAJYBXTYAUYJVVDVVKVVCT
      VUAVVCUYRBEUVHUWNGFVUJEOOUYBVAEOUWNUXTVVGOUBEWNZWOVUHEWLZWPVUNEUBUSZUXTUY
      BVAEUWNUXTWSWTYCYDYEYFZXEUXPUWQUYJUYGVASZUWLUYLAVVDUYJVVQVVEVVIVVJADVASZE
      FXSBGXSZVVLVVQAVVRBEGFAUYQUYSVVRAUYQUYSVVRKYBXTYAUYJVVDVVSVVQTVVRVVQUYEVA
      SZBEUVHUWNGFBOOUYEVAVVAVUIWPZEOOUYGVAEOUWNUYEVVGVVMWOVVNWPVUKDUYEVAVVBWTZ
      VVOUYEUYGVAEUWNUYEWSWTYCYDYEYFZXEUXSAVVDNGUYBPZQUEZNGUYGPZRAUXNUXRYGUWQVV
      DUXPUWLVVHUUCAVVDVDZBGEUWNCVSZPZQUEZBGEUWNDVSZPZVWEVWFAUYQVDZBGCPZQUEZBGD
      PZRZTVWGVWJVWLRZTEUBVWGVWREVWGEWLEOOVWJVWLEOVWIQVUGQSEWLEBOGVWHVUGGSEWLZE
      OUWNCVVGVVMWOYHUUAEBOGVWKVWSEOUWNDVVGVVMWOYHUUDWQVVOVWMVWGVWQVWRVVOUYQVVD
      AUYPUWNFXAUUBVVOVWOVWJVWPVWLVVOVWNVWIQVVOBGCVWHEUWNCWSUNUOVVOBGDVWKEUWNDW
      SUNUPUQLXBVWIVWDQBNOGVWHUYBVUGVWHSNWLBEOUWNUXTOUBBWNZVUFYLVUKUWNWASZVWHUY
      BRVVGVUKEUWNCUXTWAVUMYIYMXHVJBNOGVWKUYGVUGVWKSNWLBEOUWNUYEVWTVVAYLVUKVXAV
      WKUYGRVVGVUKEUWNDUYEWAVVBYIYMXHUUEWFUUFUXSUWSUYDQUXPUWQUWSUYDRUWLUYKUWSNG
      UWPUXTEUDZPUYDBNOGUWRVXBVUGUWRSNWLBOUWPUXTEVUGUWPSBWLZVUFXLVUKUWPCUXTEVUM
      XGXHUYKNGVXBUYCUYLVXBUYAUWOUXTEUDZVTXKUYCUYLUWEUWOUXTUWPEUYLUXNUWEUWOUUGU
      LRAUXNUWQUYJUUHUWEUWNUUIXQZUYLUWPUUJZUYLUVFUWQUWPUGSUYMUXPUWQUYJWJZFUWPWE
      WFZUYLUYPUWPSZVDZAUYQUYJUYRUYKUYJVXIAAUXNUWQUYJVXIWGWIZUYLUWPFUYPVXGWHZUY
      KUYJVXIWJZVUOXCYJUYLVXDUYBUYAVTUYLVXAVVCVXDUYBRVVGVVPUXTEUWNWAYKYNYOYPYQY
      RYSUOUXPUWQUXBUYIRUWLUYKUXBNGUWPUYEEUDZPUYIBNOGUXAVXNVUGUXASNWLBOUWPUYEEV
      XCVVAXLVUKUWPDUYEEVVBXGXHUYKNGVXNUYHUYLVXNUYFUWOUYEEUDZVTXKUYHUYLUWEUWOUY
      EUWPEVXEVXFVXHVXJAUYQUYJVVTVXKVXLVXMUYTVVRTVUBVVTTBNVUBVVTBVUCVWAWQVUKUYT
      VUBVVRVVTVULVWBUQKXBXCYJUYLVXOUYGUYFVTUYLVXAVVQVXOUYGRVVGVWCUYEEUWNWAYKYN
      YOYPYQYRYSUUNUUKYTUULUUMUUOYTUUPUUQUUR $.
      $( [12-Nov-2014] $)
  $}

  ${
    $d x N $.
    $( Derivative of an exponential, possibly zero power. $)
    dvexp2 $p |- ( N e. NN0 -> ( _D ` ( x e. RR |-> ( x ^ N ) ) ) =
        ( x e. RR |-> if ( N = 0 , 0 , ( N x. ( x ^ ( N - 1 ) ) ) ) ) ) $=
      ( wcel cc0 wceq cr cexp co cmpt cdv cfv c1 csn cxp fconstmpt syl mpteq2dv
      wa cc adantl cn0 cv cmin cmul cif ax-1cn dvconst ax-mp recn exp0 mpteq2ia
      eqtr4i fveq2i 3eqtr3i oveq2 fveq2d iftrue wn cn elnn0 orel2 syl5bi impcom
      3eqtr4a wo dvexp iffalse eqtr4d pm2.61dan ) BUACZBDEZAFAUBZBGHZIZJKZAFVKD
      BVLBLUCHGHUDHZUEZIZEVJVKRZAFVLDGHZIZJKZAFDIZVOVRFLMNZJKZFDMNZWBWCLSCWEWFE
      UFLUGUHWDWAJWDAFLIWAAFLOAFVTLVLFCVLSCVTLEVLUIVLUJPUKULUMAFDOUNVSVNWAJVKVN
      WAEVJVKAFVMVTBDVLGUOQTUPVKVRWCEVJVKAFVQDVKDVPUQQTVDVJVKURZRZVOAFVPIZVRWHB
      USCZVOWIEWGVJWJVJWJVKVEWGWJBUTVKWJVAVBVCABVFPWGVRWIEVJWGAFVQVPVKDVPVGQTVH
      VI $.
      $( [13-Nov-2014] $)
  $}

  ${
    $d ph z j k $.  $d A z j k $.  $d B z $.  $d N j k z $.
    dvply1.f $e |- ( ph -> F = ( z e. RR |-> sum_ k e. ( 0 ... N )
        ( ( A ` k ) x. ( z ^ k ) ) ) ) $.
    dvply1.g $e |- ( ph -> G = ( z e. RR |-> sum_ k e. ( 0 ... ( N - 1 ) )
        ( ( B ` k ) x. ( z ^ k ) ) ) ) $.
    dvply1.a $e |- ( ph -> A : NN0 --> CC ) $.
    dvply1.b $e |- B = ( k e. NN0 |-> ( ( k + 1 ) x. ( A ` ( k + 1 ) ) ) ) $.
    dvply1.n $e |- ( ph -> N e. NN0 ) $.
    $( Derivative of a polynomial, explicit sum version. $)
    dvply1 $p |- ( ph -> ( _D ` F ) = G ) $=
      ( cc0 co cmul c1 wcel cc cn0 vj cdv cfv cr cfz cv cexp csu cmpt wceq cmin
      cif fveq2d wss ssid fzfid wa wf elfznn0 ffvelrn syl2an adantr simpr recnd
      a1i ad2antlr expcl syl2anc mulcl 3impa w3a 3adant3 0cnALT wn simpl2 nn0cn
      3syl simpl3 cn wo elnn0 biimpi orel2 sylc nnm1nn0 syl ifclda cvv cz elexi
      0z ovex ifex adantl dvexp2 dvmptcmul cioo crn cmnf cpnf iooretop eqeltrri
      ctg ioomax dvmptfsum wne elfznn nnne0 notnot2 necon1ai iffalse oveq2d cuz
      sumeq2dv 1nn0 nn0uz eleqtri fzss1 sylancr nnnn0 df-ne nn0sscn sseldi cdif
      simplr eqeltrd caddc eldifn ax-1cn addid2i oveq1i eleq2i sylnibr ad2antrr
      eldifi wb sylancl oveq1d oveq1 oveq12d syl6eleq mpbid iftrue mul01 sylan2
      elfzp12 eqtrd fsumss pncan peano2nn0 mulass syl3anc mulcom 3eqtr2d subidi
      sumeq1i weq oveq2 cbvsumv 3eqtr4g 1z nn0z fveq2 fsumshftm 3eqtr4d 3eqtr3d
      id fvmpt2 mpteq2dva eqtr4d 3eqtrd ) AFUBUCBUDNHUEOZEUFZCUCZBUFZUVMUGOZPOZ
      EUHUIZUBUCBUDUVLUVNUVMNUJZNUVMUVOUVMQUKOZUGOZPOZULZPOZEUHZUIZGAFUVRUBIUMA
      BUVQUWDEUVLUDUDUDUNZAUDUOZVEANHUPAUVMUVLRZUVOUDRZUVQSRZAUWIUQZUWJUQZUVNSR
      ZUVPSRZUWKUWLUWNUWJATSCURZUVMTRZUWNUWIKUVMHUSZTSUVMCUTZVAZVBUWMUVOSRZUWQU
      WOUWMUVOUWLUWJVCVDUWIUWQAUWJUWRVFUVOUVMVGVHZUVNUVPVIVHVJAUWIUWJVKZUWNUWCS
      RZUWDSRZAUWIUWNUWJUWTVLUXCUVSNUWBSNSRUXCUVSUQVMVEUXCUVSVNZUQZUVMSRZUWASRZ
      UWBSRZUXGUWIUWQUXHAUWIUWJUXFVOZUWRUVMVPVQUXGUXAUVTTRZUXIUXGUVOAUWIUWJUXFV
      RVDUXGUVMVSRZUXLUXGUXFUXMUVSVTZUXMUXCUXFVCUXGUWIUWQUXNUXKUWRUWQUXNUVMWAWB
      VQUVSUXMWCWDUVMWEZWFUVOUVTVGZVHUVMUWAVIZVHWGUVNUWCVIZVHUWLBUVPUWCUVNWHUDU
      WGUWLUWHVEUXBUWCWHRUWMUVSNUWBNWIWKWJUVMUWAPWLWMVEUWLUWQBUDUVPUIUBUCBUDUWC
      UIUJUWIUWQAUWRWNBUVMWOWFUWTWPUDWQWRXCUCZRAWSWTWQOUDUXSXDWSWTXAXBVEXEAUWFB
      UDNHQUKOZUEOZUVMDUCZUVPPOZEUHZUIGABUDUWEUYDAUWJUQZQHUEOZUWDEUHUYFUVNUWBPO
      ZEUHZUWEUYDUYEUYFUWDUYGEUYEUVMUYFRZUQZUWCUWBUVNPUYJUXFUWCUWBUJZUYIUXFUYEU
      YIUXMUVMNXFZUXFUVMHXGZUVMXHZUXFUVMNUVSXIXJVQWNUVSNUWBXKZWFXLXNUYEUYFUVLUW
      DEUYEQNXMUCZRHTRZUYFUVLUNQTUYPXOXPXQAUYQUWJMVBZQNHTXRXSUYJUWNUXDUXEUYEUWP
      UWQUWNUYIAUWPUWJKVBZUYIUXMUWQUYMUVMXTWFZUWSVAZUYJUWCUWBSUYJUYLUXFUYKUYIUY
      LUYEUYIUXMUYLUYMUYNWFWNUYLUXFUVMNYAWBUYOVQUYJUXHUXIUXJUYJTSUVMYBUYIUWQUYE
      UYTWNYCUYJUXAUXLUXIUYJUVOAUWJUYIYEVDUYIUXLUYEUYIUXMUXLUYMUXOWFWNUXPVHUXQV
      HZYFUXRVHUYEUVMUVLUYFYDRZUQZUWDUVNNPOZNVUDUWCNUVNPVUDUVSUWCNUJVUDUVMNQYGO
      ZHUEOZRZVNZUVSVUHVTZUVSVUCVUIUYEVUCUYIVUHUVMUVLUYFYHVUGUYFUVMVUFQHUEQYIYJ
      YKYLYMWNVUDUWIVUJVUCUWIUYEUVMUVLUYFYOZWNVUDHUYPRZUWIVUJYPAVULUWJVUCAHTUYP
      MXPUUAYNUVMNHUUFWFUUBVUHUVSWCWDUVSNUWBUUCWFXLVUCUYEUWIVUENUJZVUKUYEUWIUQU
      WNVUMUYEUWPUWQUWNUWIUYSUWRUWSVAUVNUUDWFUUEUUGUYENHUPUUHUYEQQUKOZUXTUEOZUA
      UFZQYGOZCUCZVUQUVOVUQQUKOZUGOZPOZPOZUAUHZUYAUVMQYGOZVVDCUCZPOZUVPPOZEUHZU
      YHUYDUYEUYAVVBUAUHUYAVUQVURPOZUVOVUPUGOZPOZUAUHVVCVVHUYEUYAVVBVVKUAUYEVUP
      UYARZUQZVVBVURVUQVVJPOZPOZVURVUQPOZVVJPOZVVKVVMVVAVVNVURPVVMVUTVVJVUQPVVM
      VUSVUPUVOUGVVMVUPSRQSRVUSVUPUJVVMTSVUPYBVVLVUPTRZUYEVUPUXTUSZWNZYCYIVUPQU
      UIYQXLXLXLVVMVURSRZVUQSRZVVJSRZVVQVVOUJVVMUWPVUQTRZVWAAUWPUWJVVLKYNVVLVWD
      UYEVVLVVRVWDVVSVUPUUJWFWNZTSVUQCUTVHZVVMTSVUQYBVWEYCZVVMUXAVVRVWCVVMUVOAU
      WJVVLYEVDVVTUVOVUPVGVHVURVUQVVJUUKUULVVMVVPVVIVVJPVVMVWAVWBVVPVVIUJVWFVWG
      VURVUQUUMVHYRUUNXNVUOUYAVVBUAVUNNUXTUEQYIUUOYKUUPUYAVVGVVKEUAEUAUUQZVVFVV
      IUVPVVJPVWHVVDVUQVVEVURPUVMVUPQYGYSZVWHVVDVUQCVWIUMYTUVMVUPUVOUGUURYTUUSU
      UTUYEUYGVVBEUAQQHQWIRUYEUVAVEZVWJUYEUYQHWIRUYRHUVBWFUYJUWNUXJUYGSRVUAVUBU
      VNUWBVIVHUVMVUQUJZUVNVURUWBVVAPUVMVUQCUVCVWKUVMVUQUWAVUTPVWKUVGVWKUVTVUSU
      VOUGUVMVUQQUKYSXLYTYTUVDUYEUYAUYCVVGEUYEUVMUYARZUQZUYBVVFUVPPVWMUWQVVFWHR
      UYBVVFUJVWLUWQUYEUVMUXTUSWNVVDVVEPWLETVVFWHDLUVHYQYRXNUVEUVFUVIJUVJUVK $.
      $( [13-Nov-2014] $)
  $}

  ${
    $d S a b c p $.  $d F a b c p $.  $d D a b c p $.

    $( An infinite set of values can be extended to a polynomial in at most one
       way. $)
    plyexmo $p |- ( ( D C_ CC /\ -. D e. Fin ) -> E* p ( p e. ( Poly ` S ) /\
        ( p |` D ) = F ) ) $=
      ( va cc wcel wa cv cfv wceq cmin cc0 c0p wfn cvv wf syl adantr syl2anc vb
      wss cfn wn cply cres wmo weq wi wal cof co csn cxp ccnv cima simplr sseld
      simpll simprll plyf ffn simprrl a1i sselda fnfvof syl22anc simprlr eqtr4d
      cnex simprrr fveq1d fvres adantl 3eqtr3d ffvelrn subeq0 mpbird eqtrd jcad
      wb ex plysubcl 0cn elexi fniniseg sylancl sylibrd ssrdv ssfi expcom chash
      mtod cdgr cle wbr df-ne biimpri eqid fta1 syl2an simpld mt3d df-0p syl6eq
      ofsubeq0 syl3anc mpbid alrimivv eleq1 reseq1 eqeq1d anbi12d sylibr plyssc
      wne mo4 sseli anim1i immoi ) AFUBZAUCGZUDZHZDIZFUEJZGZYEAUFZCKZHZDUGZYEBU
      EJZGZYIHZDUGYDYJEIZYFGZYOAUFZCKZHZHZDEUHZUIZEUJDUJYKYDUUBDEYDYTUUAYDYTHZY
      EYOLUKULZFMUMZUNZKZUUAUUCUUDNUUFUUCUUDNKZUUDUOUUEUPZUCGZUUCUUJYBYAYCYTUQU
      UCAUUIUBZUUJYBUIUUCUAAUUIUUCUAIZAGZUULFGZUULUUDJZMKZHZUULUUIGZUUCUUMUUNUU
      PUUCAFUULYAYCYTUSZURUUCUUMUUPUUCUUMHZUUOUULYEJZUULYOJZLULZMUUTYEFOZYOFOZF
      PGZUUNUUOUVCKUUCUVDUUMUUCFFYEQZUVDUUCYGUVGYDYGYIYSUTZFYEVARZFFYEVBRSUUCUV
      EUUMUUCFFYOQZUVEUUCYPUVJYDYJYPYRVCZFYOVARZFFYOVBRSUVFUUTVJVDUUCAFUULUUSVE
      ZFLYEYOPUULVFVGUUTUVCMKZUVAUVBKZUUTUULYHJZUULYQJZUVAUVBUUTUULYHYQUUCYHYQK
      UUMUUCYHCYQYDYGYIYSVHYDYJYPYRVKVISVLUUMUVPUVAKUUCUULAYEVMVNUUMUVQUVBKUUCU
      ULAYOVMVNVOUUTUVAFGZUVBFGZUVNUVOWAUUTUVGUUNUVRUUCUVGUUMUVISUVMFFUULYEVPTU
      UTUVJUUNUVSUUCUVJUUMUVLSUVMFFUULYOVPTUVAUVBVQTVRVSWBVTUUCUUDFOZMPGUURUUQW
      AUUCFFUUDQZUVTUUCUUDYFGZUWAUUCYGYPUWBUVHUVKFYEYOWCTZFUUDVARFFUUDVBRMFWDWE
      FMUULUUDPWFWGWHWIUUJUUKYBUUIAWJWKRWMUUCUUHUDZUUJUUCUWDHUUJUUIWLJUUDWNJWOW
      PZUUCUWBUUDNXPZUUJUWEHUWDUWCUWFUWDUUDNWQWRUUIFUUDUUIWSWTXAXBWBXCXDXEUUCUV
      FUVGUVJUUGUUAWAUVFUUCVJVDUVIUVLFYEYOPXFXGXHWBXIYJYSDEUUAYGYPYIYRYEYOYFXJU
      UAYHYQCYEYOAXKXLXMXQXNYNYJDYMYGYIYLYFYEBXOXRXSXTR $.
      $( [14-Nov-2014] $)
  $}

  ${
    $d F a b c d e g $.
    $( The derivative of a polynomial is a polynomial up to domain
       difficulties. $)
    dvply2 $p |- ( F e. ( Poly ` S ) -> E! g e. ( Poly ` CC )
        ( _D ` ( F |` RR ) ) = ( g |` RR ) ) $=
      ( va vb vc cfv wcel cc cr wceq wa cc0 c1 co cn0 cmul cmpt cn c0 cply cres
      cdv wreu plyssc sseli wrex wmo cdgr cmin cfz caddc ccoe cexp csu wss ssid
      cv a1i nnm1nn0 adantl peano2nn0 nn0cn syl eqid coef3 ffvelrn syl2an mulcl
      wf syl2anc fmptd adantr elplyr syl3anc wn dgrcl elnn0 sylib orcanai oveq1
      c0p wo oveq2d clt wbr cneg df-neg lt01 wb 1re lt0neg2 ax-mp mpbi eqbrtrri
      cz 0z 1z zsubcl mp2an fzn syl6eq sumeq1d sum0 mpteq2dva csn cxp fconstmpt
      df-0p eqtri syl6eqr syl6eqel pm2.61dan coeid reseq1d ax-resscn resmpt weq
      fveq2d oveq12d cbvmptv dvply1 reseq1 eqeq2d rcla4ev cfn com ominf cvv cen
      ply0 omex nnenom enfi mtbir nnssre ssfi mpan2 mto plyexmo anbi2i sylanbrc
      eqcom mobii reu5 ) CAUAGZHCIUAGZHZCJUBZUCGZBURZJUBZKZBUUGUDZUUFUUGCAUEUFU
      UHUUMBUUGUGZUUKUUGHZUUMLZBUHZUUNUUHDIMCUIGZNUJOZUKOZEURZFPFURZNULOZUVDCUM
      GZGZQOZRZGDURZUVBUNOZQOZEUOZRZUUGHZUUJUVMJUBZKZUUOUUHUUSSHZUVNUUHUVQLZIIU
      PZUUTPHZPIUVHVJZUVNUVSUVRIUQZUSUVQUVTUUHUUSUTVAUUHUWAUVQUUHFPUVGIUVHUUHUV
      CPHZLUVDIHZUVFIHZUVGIHUWCUWDUUHUWCUVDPHZUWDUVCVBZUVDVCVDVAUUHPIUVEVJUWFUW
      EUWCUVEICUVEVEZVFZUWGPIUVDUVEVGVHUVDUVFVIVKUVHVEVLVMDUVHIEUUTVNVOUUHUVQVP
      LZUVMWBUUGUWJUVMDIMRZWBUWJDIUVLMUWJUVIIHZLZUVLTUVKEUOMUWMUVATUVKEUWJUVATK
      ZUWLUWJUUSMKZUWNUUHUVQUWOUUHUUSPHUVQUWOWCICVQZUUSVRVSVTUWOUVAMMNUJOZUKOZT
      UWOUUTUWQMUKUUSMNUJWAWDUWQMWEWFZUWRTKZNWGZUWQMWENWHMNWEWFZUXAMWEWFZWINJHU
      XBUXCWJWKNWLWMWNWOMWPHZUWQWPHZUWSUWTWJWQUXDNWPHUXEWQWRMNWSWTMUWQXAWTWNXBV
      DVMXCUVKEXDXBXEWBIMXFXGUWKXIDIMXHXJXKUVSWBUUGHUWBIYKWMXLXMUUHDUVEUVHEUUIU
      VOUUSUUHUUIDIMUUSUKOUVBUVEGUVJQOEUOZRZJUBZDJUXFRZUUHCUXGJDUVEIECUUSUWHUUS
      VEXNXOJIUPZUXHUXIKXPDIJUXFXQWMXBUVODJUVLRKZUUHUXJUXKXPDIJUVLXQWMUSUWIFEPU
      VGUVBNULOZUXLUVEGZQOFEXRZUVDUXLUVFUXMQUVCUVBNULWAZUXNUVDUXLUVEUXOXSXTYAUW
      PYBUUMUVPBUVMUUGUUKUVMKUULUVOUUJUUKUVMJYCYDYEVKUURUUHUUPUULUUJKZLZBUHZUUR
      UXJJYFHZVPUXRXPUXSSYFHZUXTYGYFHZYHYGYIHSYGYJWFUXTUYAWJYLYMSYGYIYNWTYOUXSS
      JUPUXTYPJSYQYRYSJIUUJBYTWTUXQUUQBUXPUUMUUPUULUUJUUCUUAUUDWNUSUUMBUUGUUEUU
      BVD $.
      $( [14-Nov-2014] $)
  $}

  $c DnNEW C^nNEW $.

  $( The ` n ` -th derivative operator. $)
  cdvnNEW $a class DnNEW $.

  $( The set of ` n ` -times continuously differentiable functions. $)
  ccpnNEW $a class C^nNEW $.


  ${
    $d x f $.
    $( Define the ` n ` -th derivative operator on functions on the reals.
       This just iterates the derivative operation according to the first
       argument. $)
    df-dvnNEW $a |- DnNEW = ( x e. NN0 , f e. ( CC ^pm RR ) |->
      ( seq 0 ( ( _D o. 1st ) , ( NN0 X. { f } ) ) ` x ) ) $.

    $( Define the set of ` n ` -times continuously differentiable functions. $)
    df-cpnNEW $a |- C^nNEW = ( x e. NN0 |-> { f e. ( CC ^pm RR ) |
                         ( x DnNEW f ) e. ( dom f -cn-> CC ) } ) $.
  $}

  ${
    $d F a b c d $.
    $( Strengthening of ~ dvf . $)
    dvf2 $p |- ( _D ` F ) : dom ( _D ` F ) --> CC $=
      ( va vd vb vc cdv cdm wcel cfv cc wf cr cpm co wss wa cv cioo cmin c0 crn
      ctg cnt weq cdiv cif cmpt csubsp cabs ccom copn copab df-dv dmmptss sseli
      ccnp cnex reex elpm2 biimpi dvf 3syl wn wceq ndmfv dmeq dm0 syl6eq feq12d
      f0 id mpbiri syl pm2.61i ) AFGZHZAFIZGZJVQKZVPAJLMNZHZAGZJAKWBLOPZVSVOVTA
      BVTCQZBQZGZRUAUBIZUCIIHDWFDCUDEQDQZWEIWDWEISNWHWDSNUENUFUGWDWFWGUHNUISUJU
      KIUPNIHPCEULFCEDBUMUNUOWAWCJLAUQURUSUTWBAVAVBVPVCVQTVDZVSAFVEWIVSTJTKJVJW
      IVRTJVQTWIVKWIVRTGTVQTVFVGVHVIVLVMVN $.
      $( [15-Nov-2014] $)
  $}

  ${
    $d F a b c $.  $d N a b c $.  $d M a b c $.

    $( Zero times iterated derivative. $)
    dvn0 $p |- ( F e. ( CC ^pm RR ) -> ( 0 DnNEW F ) = F ) $=
      ( va vb cc cr cpm co wcel cc0 cdvnNEW cdv c1st cn0 csn cxp cseq wceq 0nn0
      cfv cv ccom fveq2 sneq xpeq2d fveq1d df-dvnNEW fvex ovmpt2 mpan fvconst2g
      seqeq3d 0z mpan2 seq1i eqtrd ) ADEFGZHZIAJGZIKLUAZMANZOZIPZSZAIMHZUQURVCQ
      RBCIAMUPBTZUSMCTZNZOZIPZSVCJIVISVEIVIUBVFAQZIVIVBVJVHVAUSIVJVGUTMVFAUCUDU
      KUEBCUFIVBUGUHUIUQAUSVAIULUQVDIVASAQRMAIUPUJUMUNUO $.
      $( [15-Nov-2014] $)

    $( Successor iterated derivative. $)
    dvnp1 $p |- ( ( F e. ( CC ^pm RR ) /\ N e. NN0 ) ->
        ( ( N + 1 ) DnNEW F ) = ( _D ` ( N DnNEW F ) ) ) $=
      ( va vb co wcel cn0 cdv c1st csn cxp cc0 cseq cfv cdvnNEW wceq adantl cvv
      fvex cv cc cr cpm wa caddc ccom cuz elnn0uz seqp1 sylbi cop df-ov wfn wfo
      c1 fo1st fofn ax-mp opex fvco4 mp2an op1st fveq2i 3eqtri syl6eq peano2nn0
      simpl fveq2 xpeq2d seqeq3d fveq1d df-dvnNEW ovmpt2 syl2anc ancoms 3eqtr4d
      sneq fveq2d ) AUAUBUCEZFZBGFZUDZBUOUEEZHIUFZGAJZKZLMZNZBWGNZHNZWCAOEZBAOE
      ZHNWBWHWIWCWFNZWDEZWJWAWHWNPZVTWABLUGNFWOBUHWDWFLBUIUJQWNWIWMUKZWDNZWPINZ
      HNZWJWIWMWDULIRUMZWPRFWQWSPRRIUNWTUPRRIUQURWIWMUSRHIWPUTVAWRWIHWIWMBWGSZV
      BVCVDVEWBWCGFZVTWKWHPWAXBVTBVFQVTWAVGCDWCAGVSCTZWDGDTZJZKZLMZNZWHOWCXGNXC
      WCXGVHXDAPZWCXGWGXIXFWFWDLXIXEWEGXDAVQVIVJZVKCDVLZWCWGSVMVNWBWLWIHWAVTWLW
      IPCDBAGVSXHWIOBXGNXCBXGVHXIBXGWGXJVKXKXAVMVOVRVP $.
      $( [15-Nov-2014] $)

    $( The N-times derivative is a function. $)
    dvnf $p |- ( ( F e. ( CC ^pm RR ) /\ N e. NN0 ) ->
        ( N DnNEW F ) : dom ( N DnNEW F ) --> CC ) $=
      ( cn0 wcel cc cr cpm co cn cc0 wceq wo cdvnNEW cdm wf elnn0 wa cmin syl
      c1 cdv caddc nncn ax-1cn npcan sylancl adantl oveq1d nnm1nn0 dvnp1 sylan2
      cfv eqtr3d dvf2 dmeq feq12d mpbiri oveq1 dvn0 sylan9eqr simpl eqeltrd wss
      id cnex reex elpm2 simplbi jaodan sylan2b ) BCDAEFGHZDZBIDZBJKZLBAMHZNZEV
      OOZBPVLVMVQVNVLVMQZVOBTRHZAMHZUAULZKZVQVRVSTUBHZAMHZVOWAVRWCBAMVMWCBKZVLV
      MBEDTEDWEBUCUDBTUEUFUGUHVMVLVSCDWDWAKBUIAVSUJUKUMWBVQWANZEWAOVTUNWBVPWFEV
      OWAWBVDVOWAUOUPUQSVLVNQZVOVKDZVQWGVOAVKVNVLVOJAMHABJAMURAUSUTVLVNVAVBWHVQ
      VPFVCEFVOVEVFVGVHSVIVJ $.
      $( [16-Nov-2014] $)

    $( The set of N-times differentiable points is a subset of the domain of
       the function. $)
    dvnbss $p |- ( ( F e. ( CC ^pm RR ) /\ N e. NN0 ) ->
        dom ( N DnNEW F ) C_ dom F ) $=
      ( va vb cn0 wcel cc cr co cdvnNEW cdm wss wi cc0 wceq oveq1 sseq1d imbi2d
      dmeqd syl2anc cpm cv c1 caddc weq dvn0 ssid a1i eqsstrd w3a cdv cfv simp2
      simp1 wa dvnp1 wf dvnf simp3 cnex reex elpm2 simprbi 3ad2ant2 sstrd dvbss
      3exp a2d nn0ind impcom ) BEFAGHUAIFZBAJIZKZAKZLZVKCUBZAJIZKZVNLZMVKNAJIZK
      ZVNLZMVKDUBZAJIZKZVNLZMVKWCUCUDIZAJIZKZVNLZMVKVOMCDBVPNOZVSWBVKWKVRWAVNWK
      VQVTVPNAJPSQRCDUEZVSWFVKWLVRWEVNWLVQWDVPWCAJPSQRVPWGOZVSWJVKWMVRWIVNWMVQW
      HVPWGAJPSQRVPBOZVSVOVKWNVRVMVNWNVQVLVPBAJPSQRVKWAVNVNVKVTAAUFSVNVNLVKVNUG
      UHUIWCEFZVKWFWJWOVKWFWJWOVKWFUJZWIWEVNWPWIWDUKULZKZWEWPVKWOWIWROWOVKWFUMZ
      WOVKWFUNZVKWOUOWHWQAWCUPSTWPWEGWDUQZWEHLWRWELWPVKWOXAWSWTAWCURTWPWEVNHWOV
      KWFUSZVKWOVNHLZWFVKVNGAUQXCGHAUTVAVBVCVDVEWEWDVFTUIXBVEVGVHVIVJ $.
      $( [16-Nov-2014] $)

    $( The ` C^n ` object is a function. $)
    fncpn $p |- C^nNEW Fn NN0 $=
      ( va vb cv cdvnNEW co cdm cc ccncf wcel cr cpm crab cvv ccpnNEW df-cpnNEW
      cn0 wfn fnmpt ovex rabex a1i mprg ) ACZBCZDEUDFGHEIZBGJKEZLZMIZNPQAPAPUGN
      MABORUHUCPIUEBUFGJKSTUAUB $.
      $( [16-Nov-2014] $)

    $( Condition for n-times continuous differentiability. $)
    elcpn $p |- ( N e. NN0 -> ( F e. ( C^nNEW ` N ) <-> ( F e. ( CC ^pm RR ) /\
          ( N DnNEW F ) e. ( dom F -cn-> CC ) ) ) ) $=
      ( vb va cn0 wcel ccpnNEW cfv cv cdvnNEW co cdm cc ccncf cr cpm crab oveq1
      wa wceq eleq1d rabbidv df-cpnNEW ovex rabex fvmpt eleq2d oveq2 dmeq elrab
      oveq1d eleq12d syl6bb ) BEFZABGHZFABCIZJKZUPLZMNKZFZCMOPKZQZFAVAFBAJKZALZ
      MNKZFZSUNUOVBADBDIZUPJKZUSFZCVAQVBEGVGBTZVIUTCVAVJVHUQUSVGBUPJRUAUBDCUCUT
      CVAMOPUDUEUFUGUTVFCAVAUPATZUQVCUSVEUPABJUHVKURVDMNUPAUIUKULUJUM $.
      $( [15-Nov-2014] $)

    $( ` C^n ` conditions are ordered by strength. $)
    cpnord $p |- ( ( M e. NN0 /\ N e. NN0 /\ M <_ N ) ->
        ( C^nNEW ` N ) C_ ( C^nNEW ` M ) ) $=
      ( va cn0 wcel cle wbr ccpnNEW cfv wss wi co fveq2 sseq1d imbi2d cc0 cr cc
      wceq cdm vb w3a simp1 cz nn0z id cv c1 caddc weq ssid a1i12 wa simpl2 0re
      a1i nn0re adantl zre syl nn0ge0 simpl3 letrd elnn0z sylanbrc cpm ccncf wf
      cdvnNEW cdv simp2 dvnf syl2anc dvnbss dvnp1 dmeqd cncff mpan fdm 3ad2ant3
      eqtr3d cnex elpm2 simprbi 3ad2ant2 sstrd dvbss eqsstr3d eqssd feq2d mpbid
      reex dvcn syl3anc 3exp imdistand peano2nn0 elcpn 3imtr4d ssrdv sstr2 3syl
      wb ex a2d uzind syl3an mpd ) ADEZBDEZABFGZUBXIBHIZAHIZJZXIXJXKUCXIAUDEZXJ
      BUDEXKXKXIXNKZAUEBUEXKUFXICUGZHIZXMJZKXIXMXMJZKXIUAUGZHIZXMJZKXIYAUHUILZH
      IZXMJZKXPCUAABXQASZXSXTXIYGXRXMXMXQAHMNOCUAUJZXSYCXIYHXRYBXMXQYAHMNOXQYDS
      ZXSYFXIYIXRYEXMXQYDHMNOXQBSZXSXNXIYJXRXLXMXQBHMNOXOXIXTXMUKULXOYAUDEZAYAF
      GZUBZXIYCYFYMXIYCYFKZYMXIUMZYADEZYEYBJYNYOYKPYAFGYPXOYKYLXIUNZYOPAYAPQEYO
      UOUPXIAQEYMAUQURYOYKYAQEYQYAUSUTXIPAFGYMAVAURXOYKYLXIVBVCYAVDVEYPCYEYBYPX
      QRQVFLEZYDXQVILZXQTZRVGLZEZUMZYRYAXQVILZUUAEZUMXQYEEZXQYBEYPYRUUBUUEYPYRU
      UBUUEYPYRUUBUBZYTRUUDVHZYTQJZUUDVJIZTZYTSUUEUUGUUDTZRUUDVHZUUHUUGYRYPUUMY
      PYRUUBVKZYPYRUUBUCZXQYAVLVMZUUGUULYTRUUDUUGUULYTUUGYRYPUULYTJUUNUUOXQYAVN
      VMZUUGYTUUKUULUUGYSTZUUKYTUUGYSUUJUUGYRYPYSUUJSUUNUUOXQYAVOVMVPUUBYPUURYT
      SZYRUUBYTRYSVHZUUSRRJUUBUUTRUKYTRYSVQVRYTRYSVSUTVTWAZUUGUUMUULQJUUKUULJUU
      PUUGUULYTQUUQYRYPUUIUUBYRYTRXQVHUUIRQXQWBWLWCWDWEZWFUULUUDWGVMWHWIWJWKUVB
      UVAYTUUDWMWNWOWPYPYDDEUUFUUCXCYAWQXQYDWRUTXQYAWRWSWTYEYBXMXAXBXDXEXFXGXH
      $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d F a b c d g $.  $d N a b c d g $.

    $( Polynomials have polynomials as derivatives of all orders. $)
    dvnply $p |- ( ( F e. ( Poly ` S ) /\ N e. NN0 ) -> E! g e. ( Poly ` CC )
        ( g |` RR ) = ( N DnNEW ( F |` RR ) ) ) $=
      ( va cfv wcel wa cr cdvnNEW co wceq cc wrex wi oveq1 eqeq2d rexbidv cvv
      cn vb cply cn0 cv cres wmo wreu plyssc sseli cc0 caddc imbi2d weq cpm wss
      c1 plyf ax-resscn fssres sylancl ssid cnex reex elpm2r mpanl12 syl eqcomd
      wf dvn0 reseq1 eqeq1d rcla4ev mpdan dvply2 reurex ad2antrl simplrr fveq2d
      cdv simpllr simplll dvnp1 syl2anc eqeq1 syl5ibcom reximdva exp32 rexlimdv
      eqtr4d mpd cbvrexv syl6ib ex a2d nn0ind mpan9 cfn wn com ominf cen wbr wb
      omex nnenom enfi mp2an mtbir nnssre ssfi mpan2 mto plyexmo reu5 sylanbrc
      a1i ) CAUBFZGZDUCGZHZBUDZIUEZDCIUEZJKZLZBMUBFZNZYAYFGZYEHBUFZYEBYFUGXRCYF
      GZXSYGXQYFCAUHUIYJYBEUDZYCJKZLZBYFNZOYJYBUJYCJKZLZBYFNZOYJYBUAUDZYCJKZLZB
      YFNZOYJYBYRUPUKKZYCJKZLZBYFNZOYJYGOEUADYKUJLZYNYQYJUUFYMYPBYFUUFYLYOYBYKU
      JYCJPQRULEUAUMZYNUUAYJUUGYMYTBYFUUGYLYSYBYKYRYCJPQRULYKUUBLZYNUUEYJUUHYMU
      UDBYFUUHYLUUCYBYKUUBYCJPQRULYKDLZYNYGYJUUIYMYEBYFUUIYLYDYBYKDYCJPQRULYJYC
      YOLZYQYJYOYCYJYCMIUNKGZYOYCLYJIMYCVHZIIUOZUUKYJMMCVHIMUOZUULMCUQURMMICUSU
      TIVAMSGISGUULUUMHUUKVBVCMIIYCSSVDVEUTZYCVIVFVGYPUUJBCYFYACLYBYCYOYACIVJVK
      VLVMYRUCGZYJUUAUUEUUPYJUUAUUEOUUPYJHZUUAYKIUEZUUCLZEYFNZUUEUUQYTUUTBYFUUQ
      YHYTUUTUUQYHYTHZHZYBVSFZUURLZEYFNZUUTYHUVEUUQYTYHUVDEYFUGUVEMEYAVNUVDEYFV
      OVFVPUVBUVDUUSEYFUVBYKYFGZHZUVCUUCLUVDUUSUVGUVCYSVSFZUUCUVGYBYSVSUUQYHYTU
      VFVQVRUVGUUKUUPUUCUVHLUVGYJUUKUUPYJUVAUVFVTUUOVFUUPYJUVAUVFWAYCYRWBWCWIUV
      CUURUUCWDWEWFWJWGWHUUSUUDEBYFEBUMUURYBUUCYKYAIVJVKWKWLWMWNWOWPYIXTUUNIWQG
      ZWRYIURUVITWQGZUVJWSWQGZWTWSSGTWSXAXBUVJUVKXCXDXETWSSXFXGXHUVITIUOUVJXIIT
      XJXKXLIMYDBXMXGXPYEBYFXNXO $.
      $( [15-Nov-2014] $)

    $( Polynomials are smooth. $)
    plycpn $p |- ( F e. ( Poly ` S ) -> ( F |` RR ) e. |^| ran C^nNEW ) $=
      ( va vb cply cfv wcel cc cr cres ccpnNEW cn0 wb wa co ccncf wss ax-resscn
      wceq syl crn cint plyssc sseli cv wral wrex wfn fncpn fvelrnb cpm cdvnNEW
      ax-mp cdm elcpn adantl wf plyf fssres sylancl reex cnex fpm adantr dvnply
      wreu reurex plycn ssid rescncf mp2an fdm syl5sseqr ssdmres sylib ad2antrr
      wi oveq1d eleqtrrd eleq1 syl5ibcom rexlimdva mpd mpbir2and eleq2 ralrimiv
      syl5bi cvv resexg elintg mpbird ) BAEFZGBHEFZGZBIJZKUAZUBGZWLWMBAUCUDWNWQ
      WOCUEZGZCWPUFZWNWSCWPWRWPGZDUEZKFZWRSZDLUGZWNWSKLUHXAXEMUIDLWRKUJUMWNXDWS
      DLWNXBLGZNZWOXCGZXDWSXGXHWOHIUKOGZXBWOULOZWOUNZHPOZGZXFXHXIXMNMWNWOXBUOUP
      WNXIXFWNIHWOUQZXIWNHHBUQZIHQZXNHBURZRHHIBUSUTIHWOVAVBVCTVDXGWRIJZXJSZCWMU
      GZXMXGXSCWMVFXTHCBXBVEXSCWMVGTXGXSXMCWMXGWRWMGZNZXRXLGXSXMYBXRIHPOZXLYAXR
      YCGZXGYAWRHHPOGZYDHWRVHHHQXPYEYDVQHVIRHHIWRVJVKTUPYBXKIHPWNXKISZXFYAWNIBU
      NZQYFWNHIYGRWNXOYGHSXQHHBVLTVMIBVNVOVPVRVSXRXJXLVTWAWBWCWDXCWRWOWEWAWBWGW
      FWNWOWHGWQWTMBIWMWICWOWPWHWJTWKT $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d ph x y a b $.  $d A x y a b $.  $d B x y a b $.  $d F x y a b $.
    c1liplem1.a $e |- ( ph -> A e. RR ) $.
    c1liplem1.b $e |- ( ph -> B e. RR ) $.
    c1liplem1.le $e |- ( ph -> A <_ B ) $.
    c1liplem1.f $e |- ( ph -> F e. ( CC ^pm RR ) ) $.
    c1liplem1.dv $e |- ( ph -> ( ( _D ` F ) |` ( A [,] B ) ) e.
        ( ( A [,] B ) -cn-> RR ) ) $.
    c1liplem1.cn $e |- ( ph -> ( F |` ( A [,] B ) ) e.
        ( ( A [,] B ) -cn-> RR ) ) $.
    c1liplem1.k $e |- K = sup ( ( abs " ( ( _D ` F ) " ( A [,] B ) ) ) ,
        RR , < ) $.
    $( Lemma for ~ c1lip1 . $)
    c1liplem1 $p |- ( ph -> ( K e. RR /\ A. x e. ( A [,] B )
        A. y e. ( A [,] B ) ( x < y -> ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_
          ( K x. ( abs ` ( y - x ) ) ) ) ) ) $=
      ( cr wcel cfv cabs cle cc vb va cv clt wbr cmin co cmul wi cicc wral cima
      cdv csup wss c0 wne wrex crn imassrn wf absf frn ax-mp sstri a1i wfun cdm
      dvf2 ffun cres wceq ccncf ax-resscn sylancr fdm syl ssdmres sylibr lbicc2
      cncff syl3anc funfvima2 imp syl21anc fdmi sseqtr4i mp2an ne0i 3syl cncfss
      wa ssid sseldi cniccbdd fvelima mpan fvres adantl fveq2d weq fveq2 breq1d
      rcla4cva eqbrtrrd adantll syl5ibcom rexlimdva breq1 ralrimiv reximdva mpd
      syl5 suprcl syl5eqel cdiv simplrr ad2antrr ffvelrn syl2anc recnd eqeltrrd
      ex simplrl subcl iccssre sseldd resubcl simpr wb difrp mpbid rpne0 absdiv
      cc0 crp divcl cioo eqtrd sylib ltle ubicc2 oveq12d oveq1d iccss2 syl22anc
      syl6eleqr resabs1 rescncf ctg cnt cpm cnex reex elpm2 simplbi eqid iccntr
      simprbi dvres reseq2d dmeqd ioossicc syl5ss sstrd fveq1d adantrr ad2antll
      mvth sseld impr eqeltrd eleq1 rexlimdv funfvima suprub syl31anc syl6breqr
      expr abscl absrpcl elrp ledivmul rpcn mulcom breqtrd ralrimivva jca ) AGO
      PZBUCZCUCZUDUEZUWKFQZUWJFQZUFUGZRQZGUWKUWJUFUGZRQZUHUGZSUEZUIZCDEUJUGZUKB
      UXBUKAGRFUMQZUXBULZULZOUDUNZONAUXEOUOZUXEUPUQZUAUCZUBUCZSUEZUAUXEUKZUBOUR
      ZUXFOPUXGAUXERUSZORUXDUTTORVAZUXNOUOVBTORVCVDVEZVFADUXCQZUXDPZUXQRQZUXEPZ
      UXHAUXCVGZUXBUXCVHZUOZDUXBPZUXRUYAAUYBTUXCVAZUYAFVIZUYBTUXCVJVDZVFAUXCUXB
      VKZVHUXBVLZUYCAUXBOUYHVAZUYIAOTUOZUYHUXBOVMUGZPUYJVNLUXBOUYHWAVOUXBOUYHVP
      VQUXBUXCVRVSZADOPZEOPZDESUEUYDHIJDEVTWBUYAUYCWLZUYDUXRUXBDUXCWCWDWERVGZUX
      DRVHZUOUXRUXTUIUXOUYQVBTORVJVDZUXDTUYRUXDUXCUSZTUXCUXBUTUYEUYTTUOUYFUYBTU
      XCVCVDVETORVBWFZWGUXDUXQRWCWHUXEUXSWIWJZAUWJUYHQZRQZUXJSUEZBUXBUKZUBOURZU
      XMAUYNUYOUYHUXBTVMUGZPVUGHIAUYLVUHUYHUYKTTUOUYLVUHUOVNTWMUXBOTWKWHLWNUBBD
      EUYHWOWBAVUFUXLUBOAUXJOPWLZVUFUXLVUIVUFWLZUXKUAUXEUXIUXEPZUWKRQZUXIVLZCUX
      DURZVUJUXKUYQVUKVUNUYSCUXIUXDRWPWQVUJVUMUXKCUXDVUJUWKUXDPZWLVULUXJSUEZVUM
      UXKVUJVUOVUPVUOUXIUXCQZUWKVLZUAUXBURZVUJVUPUYAVUOVUSUYGUAUWKUXBUXCWPWQVUJ
      VURVUPUAUXBVUJUXIUXBPZWLVUQRQZUXJSUEZVURVUPVUFVUTVVBVUIVUFVUTWLZUXIUYHQZR
      QZVVAUXJSVVCVVDVUQRVUTVVDVUQVLVUFUXIUXBUXCWRWSWTVUEVVEUXJSUEBUXIUXBBUAXAZ
      VUDVVEUXJSVVFVUCVVDRUWJUXIUYHXBWTXCXDXEXFVURVVAVULUXJSVUQUWKRXBXCXGXHXMWD
      VULUXIUXJSXIXGXHXMXJYCXKXLZUBUAUXEXNWBXOZAUXABCUXBUXBAUWJUXBPZUWKUXBPZWLZ
      WLZUWLUWTVVLUWLWLZUWPUWRGUHUGZUWSSVVMUWPUWRXPUGZGSUEZUWPVVNSUEZVVMUWOUWQX
      PUGZRQZVVOGSVVMUWOTPZUWQTPZUWQYOUQZVVSVVOVLVVMUWMTPUWNTPVVTVVMUWKFUXBVKZQ
      ZUWMTVVMVVJVWDUWMVLAVVIVVJUWLXQZUWKUXBFWRVQVVMVWDVVMUXBOVWCVAZVVJVWDOPAVW
      FVVKUWLAUYKVWCUYLPZVWFVNMUXBOVWCWAVOXRZVWEUXBOUWKVWCXSXTYAYBVVMUWJVWCQZUW
      NTVVMVVIVWIUWNVLAVVIVVJUWLYDZUWJUXBFWRVQVVMVWIVVMVWFVVIVWIOPVWHVWJUXBOUWJ
      VWCXSXTYAYBUWMUWNYEXTZVVMUWQVVMUWKOPZUWJOPZUWQOPVVMUXBOUWKAUXBOUOZVVKUWLA
      UYNUYOVWNHIDEYFXTXRZVWEYGZVVMUXBOUWJVWOVWJYGZUWKUWJYHXTYAZVVMUWQYPPZVWBVV
      MUWLVWSVVLUWLYIZVVMVWMVWLUWLVWSYJVWQVWPUWJUWKYKXTYLUWQYMVQZUWOUWQYNWBVVMV
      VSUXFGSVVMUXGUXHUXMVVSUXEPZVVSUXFSUEUXGVVMUXPVFAUXHVVKUWLVUBXRAUXMVVKUWLV
      VGXRVVMUYQVVRUYRPZVVRUXDPZVXBUYQVVMUYSVFVVMVVRTUYRVVMVVTVWAVWBVVRTPVWKVWR
      VXAUWOUWQYQWBVUAUUGVVMUWKFUWJUWKUJUGZVKZQZUWJVXFQZUFUGZUWQXPUGZVVRUXDVVMV
      XIUWOUWQXPVVMVXGUWMVXHUWNUFVVMUWKVXEPZVXGUWMVLVVMVWMVWLUWJUWKSUEZVXKVWQVW
      PVVMUWLVXLVWTVVMVWMVWLUWLVXLUIVWQVWPUWJUWKUUAXTXLZUWJUWKUUBWBUWKVXEFWRVQV
      VMUWJVXEPZVXHUWNVLVVMVWMVWLVXLVXNVWQVWPVXMUWJUWKVTWBUWJVXEFWRVQUUCUUDVVMU
      XJVXFUMQZQZVXJVLZUBUWJUWKYRUGZURVXJUXDPZVVMUBUWJUWKVXFVWQVWPVWTVVMVWCVXEV
      KZVXFVXEOVMUGZVVMVXEUXBUOZVXTVXFVLVVMUYNUYOVVIVVJVYBAUYNVVKUWLHXRAUYOVVKU
      WLIXRVWJVWEUYNUYOWLVVKVYBDEUWJUWKUUEWDUUFZFVXEUXBUUHVQVVMUYKVYBVWGVXTVYAP
      ZUYKVVMVNVFVYCAVWGVVKUWLMXRUYKVYBWLVWGVYDUXBOVXEVWCUUIWDWEYBVVMVXOVHUXCVX
      RVKZVHZVXRVVMVXOVYEVVMVXOUXCVXEYRUSUUJQZUUKQQZVKZVYEVVMFVHZTFVAZVYJOUOZVX
      EOUOZVXOVYIVLVVMFTOUULUGPZVYKAVYNVVKUWLKXRZVYNVYKVYLTOFUUMUUNUUOZUUPVQVVM
      VYNVYLVYOVYNVYKVYLVYPUUSVQVVMVWMVWLVYMVWQVWPUWJUWKYFXTVYJVXEVYGFVYGUUQUUT
      WBVVMVYHVXRUXCVVMVWMVWLVYHVXRVLVWQVWPUWJUWKUURXTUVAYSZUVBVVMVXRUYBUOVYFVX
      RVLVVMVXRUXBUYBVVMVXRVXEUXBUWJUWKUVCVYCUVDZAUYCVVKUWLUYMXRUVEVXRUXCVRYTYS
      UVIVVMVXQVXSUBVXRVVLUWLUXJVXRPZVXQVXSUIVVLUWLVYSWLZWLZVXPUXDPVXQVXSWUAVXP
      UXJUXCQZUXDWUAVXPUXJVYEQZWUBVVLUWLVXPWUCVLVYSVVMUXJVXOVYEVYQUVFUVGVYSWUCW
      UBVLVVLUWLUXJVXRUXCWRUVHYSWUAUYAUYCUXJUXBPZWUBUXDPZUYAWUAUYGVFAUYCVVKVYTU
      YMXRVVLUWLVYSWUDVVMVXRUXBUXJVYRUVJUVKUYPWUDWUEUXBUXJUXCWCWDWEUVLVXPVXJUXD
      UVMXGUVSUVNXLYBUYQVXCWLVXDVXBUXDVVRRUVOWDWEUBUAUXEVVSUVPUVQNUVRXEVVMUWPOP
      ZUWIUWROPYOUWRUDUEWLZVVPVVQYJVVMVVTWUFVWKUWOUVTVQAUWIVVKUWLVVHXRZVVMUWRYP
      PZWUGVVMVWAVWBWUIVWRVXAUWQUWAXTZUWRUWBYTUWPGUWRUWCWBYLVVMUWRTPZGTPVVNUWSV
      LVVMWUIWUKWUJUWRUWDVQVVMGWUHYAUWRGUWEXTUWFYCUWGUWH $.
      $( [15-Nov-2014] $)
  $}

  ${
    $d ph x y k a b $.  $d A x y k a b $.  $d B x y k a b $.  $d F x y k a b $.
    c1lip1.a $e |- ( ph -> A e. RR ) $.
    c1lip1.b $e |- ( ph -> B e. RR ) $.
    c1lip1.f $e |- ( ph -> F e. ( CC ^pm RR ) ) $.
    c1lip1.dv $e |- ( ph -> ( ( _D ` F ) |` ( A [,] B ) ) e.
        ( ( A [,] B ) -cn-> RR ) ) $.
    c1lip1.cn $e |- ( ph -> ( F |` ( A [,] B ) ) e.
        ( ( A [,] B ) -cn-> RR ) ) $.
    $( C1 functions are Lipschitz continuous on closed intervals. $)
    c1lip1 $p |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B )
        ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_
          ( k x. ( abs ` ( y - x ) ) ) ) $=
      ( cfv cmin co cabs cle cr cc0 wcel va vb cv cmul wbr cicc wral wrex wa c0
      clt wne 0re ne0i ax-mp ral0 wceq cxr wb rexr icc0 syl2anc biimpar raleqdv
      syl mpbiri ralrimivw r19.2z sylancr wi cdv cima csup adantr simpr cc cres
      cpm ccncf eqid c1liplem1 oveq1 breq2d imbi2d 2ralbidv rcla4ev weq w3o wss
      iccssre ad2antrr sseld anim12d imp lttri4 breq1 fveq2 oveq2d fveq2d oveq2
      breq12d imbi12d breq2 oveq1d rcla42v ad2antlr pm2.27 adantl syld 0nn0 a1i
      nn0ge0i fvres ad2antrl ax-resscn cncff simpl ffvelrn eqeltrrd recnd subid
      syl2an abs0 syl6eq ad3antrrr simprl sseldd simplr mul01 3brtr4d syl5ibcom
      wf eqtrd a1d ancoms ad2antll abssub recn biimpd embantd 3jaodan mpdan mpd
      ralrimdvva reximdva pm2.61ltlei ) ACUCZGMZBUCZGMZNOZPMZFUCZUUGUUINOZPMZUD
      OZQUEZCDEUFOZUGZBUURUGZFRUHZEDAEDUKUEZUIZRUJULZUUTFRUGUVASRTUVDUMRSUNUOUV
      CUUTFRUVCUUTUUSBUJUGUUSBUPUVCUUSBUURUJAUURUJUQZUVBADURTZEURTZUVEUVBUSADRT
      ZUVFHDUTVEAERTZUVGIEUTVEDEVAVBVCVDVFVGUUTFRVHVIADEQUEZUIZUAUCZUBUCZUKUEZU
      VMGMZUVLGMZNOZPMZUUMUVMUVLNOZPMZUDOZQUEZVJZUBUURUGUAUURUGZFRUHZUVAUVKPGVK
      MZUURVLVLRUKVMZRTUVNUVRUWGUVTUDOZQUEZVJZUBUURUGUAUURUGZUIUWEUVKUAUBDEGUWG
      AUVHUVJHVNAUVIUVJIVNAUVJVOAGVPRVROTUVJJVNAUWFUURVQUURRVSOZTUVJKVNAGUURVQZ
      UWLTZUVJLVNUWGVTWAUWDUWKFUWGRUUMUWGUQZUWCUWJUAUBUURUURUWOUWBUWIUVNUWOUWAU
      WHUVRQUUMUWGUVTUDWBWCWDWEWFVEUVKUWDUUTFRUVKUUMRTZUIZUWDUUQBCUURUURUWQUUIU
      URTZUUGUURTZUIZUIZUUIUUGUKUEZBCWGZUUGUUIUKUEZWHZUWDUUQVJZUXAUUIRTZUUGRTZU
      IZUXEUWQUWTUXIUWQUWRUXGUWSUXHUWQUURRUUIAUURRWIZUVJUWPAUVHUVIUXJHIDEWJVBZW
      KZWLUWQUURRUUGUXLWLWMWNZUUIUUGWOVEUXAUXBUXFUXCUXDUXAUXBUIUWDUXBUUQVJZUUQU
      WTUWDUXNVJUWQUXBUWCUXNUUIUVMUKUEZUVOUUJNOZPMZUUMUVMUUINOZPMZUDOZQUEZVJUAU
      BUUIUUGUURUURUABWGZUVNUXOUWBUYAUVLUUIUVMUKWPUYBUVRUXQUWAUXTQUYBUVQUXPPUYB
      UVPUUJUVONUVLUUIGWQWRWSUYBUVTUXSUUMUDUYBUVSUXRPUVLUUIUVMNWTWSWRXAXBUBCWGZ
      UXOUXBUYAUUQUVMUUGUUIUKXCUYCUXQUULUXTUUPQUYCUXPUUKPUYCUVOUUHUUJNUVMUUGGWQ
      XDWSUYCUXSUUOUUMUDUYCUXRUUNPUVMUUGUUINWBWSWRXAXBXEXFUXBUXNUUQVJUXAUXBUUQX
      GXHXIUXAUXCUIUUQUWDUXAUXCUUQUXAUUJUUJNOZPMZUUMUUIUUINOZPMZUDOZQUEUXCUUQUX
      ASSUYEUYHQSSQUEUXASXJXLXKUXAUYESPMZSUXAUYDSPUXAUUJVPTZUYDSUQUXAUUJUXAUUIU
      WMMZUUJRUWRUYKUUJUQUWQUWSUUIUURGXMXNUWQUURRUWMYLZUWRUYKRTUWTAUYLUVJUWPARV
      PWIUWNUYLXOLUURRUWMXPVIWKZUWRUWSXQUURRUUIUWMXRYBXSXTZUUJYAVEWSYCYDUXAUYHU
      UMSUDOZSUXAUYGSUUMUDUXAUYGUYISUXAUYFSPUXAUUIVPTZUYFSUQUXAUUIUXAUURRUUIAUX
      JUVJUWPUWTUXKYEUWQUWRUWSYFYGXTUUIYAVEWSYCYDWRUXAUUMVPTUYOSUQUXAUUMUVKUWPU
      WTYHXTUUMYIVEYMYJUXCUYEUULUYHUUPQUXCUYDUUKPUXCUUJUUHUUJNUUIUUGGWQXDWSUXCU
      YGUUOUUMUDUXCUYFUUNPUUIUUGUUINWBWSWRXAYKWNYNUXAUXDUIZUWDUXDUUJUUHNOZPMZUU
      MUUIUUGNOZPMZUDOZQUEZVJZUUQUWTUWDVUDVJZUWQUXDUWSUWRVUEUWCVUDUUGUVMUKUEZUV
      OUUHNOZPMZUUMUVMUUGNOZPMZUDOZQUEZVJUAUBUUGUUIUURUURUACWGZUVNVUFUWBVULUVLU
      UGUVMUKWPVUMUVRVUHUWAVUKQVUMUVQVUGPVUMUVPUUHUVONUVLUUGGWQWRWSVUMUVTVUJUUM
      UDVUMUVSVUIPUVLUUGUVMNWTWSWRXAXBUBBWGZVUFUXDVULVUCUVMUUIUUGUKXCVUNVUHUYSV
      UKVUBQVUNVUGUYRPVUNUVOUUJUUHNUVMUUIGWQXDWSVUNVUJVUAUUMUDVUNVUIUYTPUVMUUIU
      UGNWBWSWRXAXBXEYOXFUYQUXDVUCUUQUXAUXDVOUYQVUCUUQUYQUYSUULVUBUUPQUXAUYSUUL
      UQZUXDUXAUYJUUHVPTVUOUYNUXAUUHUXAUUGUWMMZUUHRUWSVUPUUHUQUWQUWRUUGUURGXMYP
      UWQUYLUWSVUPRTUWTUYMUWRUWSVOUURRUUGUWMXRYBXSXTUUJUUHYQVBVNUYQVUAUUOUUMUDU
      XAVUAUUOUQZUXDUXAUXIVUQUXMUXGUYPUUGVPTVUQUXHUUIYRUUGYRUUIUUGYQYBVEVNWRXAY
      SYTXIUUAUUBUUDUUEUUCIHUUF $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d ph x y k a b $.  $d A x y k a b $.  $d B x y k a b $.  $d F x y k a b $.
    c1lip2.a $e |- ( ph -> A e. RR ) $.
    c1lip2.b $e |- ( ph -> B e. RR ) $.
    c1lip2.f $e |- ( ph -> F e. ( C^nNEW ` 1 ) ) $.
    c1lip2.rn $e |- ( ph -> ran F C_ RR ) $.
    c1lip2.dm $e |- ( ph -> ( A [,] B ) C_ dom F ) $.
    $( C1 functions are Lipschitz continuous on closed intervals. $)
    c1lip2 $p |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B )
        ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_
          ( k x. ( abs ` ( y - x ) ) ) ) $=
      ( va c1 wcel cc cr co syl cc0 ccpnNEW cfv cpm cdvnNEW cdm ccncf cn0 wa wb
      1nn0 elcpn ax-mp simplbi wss cicc cdv cres ax-resscn caddc ax-1cn addid2i
      oveq1i wceq 0nn0 dvnp1 sylancl syl5eqr dvn0 fveq2d eqtrd simprbi eqeltrrd
      a1i cv wral wi ssid wf cle wbr nn0ge0i cpnord mp3an sseldi crn wfun pmfun
      adantr fvelrn sylan sseldd ralrimiva cncffvrn syl3anc mpd cncff cnex reex
      sylancr elpm2 dvfre syl2anc fdm eleq2d biimpar ffvelrn rescncf imp c1lip1
      syl21anc ) ABCDEFGHIAGNUAUBZOZGPQUCROZJXLXMNGUDRZGUEZPUFRZOZNUGOZXLXMXQUH
      UIUJGNUKULZUMSZAQPUNZDEUORZXOUNZGUPUBZXOQUFRZOZYDYBUQYBQUFRZOZYAAURVMZLAY
      DXPOZYFAXNYDXPAXNTGUDRZUPUBZYDAXNTNUSRZGUDRZYLYMNGUDNUTVAVBAXMTUGOZYNYLVC
      XTVDGTVEVFVGAYKGUPAXMYKGVCXTGVHSZVIVJAXLXQJXLXMXQXSVKSVLZAPPUNZYAMVNZYDUB
      QOZMXOVOYJYFVPYRAPVQZVMZYIAYTMXOAYSXOOZUHZYDUEZQYDVRZYSUUEOZYTAUUFUUCAXOQ
      GVRZXOQUNZUUFAYAGYEOZUUHURAGXPOZUUJAYKGXPYPAGTUAUBZOZYKXPOZAXKUULGYOXRTNV
      SVTXKUULUNVDUJNUJWATNWBWCJWDUUMXMUUNYOUUMXMUUNUHUIVDGTUKULVKSVLAYRYAYSGUB
      ZQOZMXOVOUUKUUJVPUUBYIAUUPMXOUUDGWEZQUUOAUUQQUNUUCKWHAGWFZUUCUUOUUQOAXMUU
      RXTPQGWGSYSGWIWJWKWLMXOPQGWMWNWOZXOQGWPWSAXMUUIXTXMXOPGVRUUIPQGWQWRWTVKSX
      OGXAXBWHAUUGUUCAUUEXOYSAYRYJUUEXOVCZUUAYQYRYJUHXOPYDVRUUTXOPYDWPXOPYDXCSW
      SXDXEUUEQYSYDXFXBWLMXOPQYDWMWNWOYAYCUHZYFYHXOQYBYDXGXHXJAYAYCUUJGYBUQYGOZ
      YILUUSUVAUUJUVBXOQYBGXGXHXJXI $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d ph x y k a b $.  $d A x y k a b $.  $d B x y k a b $.  $d F x y k a b $.
    c1lip3.a $e |- ( ph -> A e. RR ) $.
    c1lip3.b $e |- ( ph -> B e. RR ) $.
    c1lip3.f $e |- ( ph -> ( F |` RR ) e. ( C^nNEW ` 1 ) ) $.
    c1lip3.rn $e |- ( ph -> ( F " RR ) C_ RR ) $.
    c1lip3.dm $e |- ( ph -> ( A [,] B ) C_ dom F ) $.
    $( C1 functions are Lipschitz continuous on closed intervals. $)
    c1lip3 $p |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B )
        ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_
          ( k x. ( abs ` ( y - x ) ) ) ) $=
      ( cr cfv cmin co cabs wral wcel wa cres cmul cle wbr cicc wrex crn df-ima
      cima syl5eqssr cdm cin wss iccssre syl2anc ssin bicomi sylanbrc syl6sseqr
      cv dmres c1lip2 sseld anim12d imp oveqan12rd fveq2d breq1d biimpd anassrs
      wi fvres syl ralimdva reximdv mpd ) ACUTZGMUAZNZBUTZVRNZOPZQNZFUTVQVTOPQN
      UBPZUCUDZCDEUEPZRZBWFRZFMUFVQGNZVTGNZOPZQNZWDUCUDZCWFRZBWFRZFMUFABCDEFVRH
      IJAVRUGGMUIMGMUHKUJAWFMGUKZULZVRUKAWFMUMZWFWPUMZWFWQUMZADMSEMSWRHIDEUNUOZ
      LWRWSTWTWFMWPUPUQURGMVAUSVBAWHWOFMAWGWNBWFAVTWFSZTWEWMCWFAXBVQWFSZWEWMVKZ
      AXBXCTZTVTMSZVQMSZTZXDAXEXHAXBXFXCXGAWFMVTXAVCAWFMVQXAVCVDVEXHWEWMXHWCWLW
      DUCXHWBWKQXGXFVSWIWAWJOVQMGVLVTMGVLVFVGVHVIVMVJVNVNVOVP $.
      $( [16-Nov-2014] $)
  $}

  ${
    $( Membership in a closed real interval. $)
    elicc4 $p |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) ->
        ( C e. ( A [,] B ) <-> ( A <_ C /\ C <_ B ) ) ) $=
      ( cxr wcel w3a cicc co cle wbr wa wb elicc1 3adant3 3anass baibr 3ad2ant3
      bitr4d ) ADEZBDEZCDEZFCABGHEZUAACIJZCBIJZFZUCUDKZSTUBUELUAABCMNUASUFUELTU
      EUAUFUAUCUDOPQR $.
      $( [16-Nov-2014] $)

    $( Membership in a symmetric closed real interval. $)
    elicc4abs $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
        ( C e. ( ( A - B ) [,] ( A + B ) ) <-> ( abs ` ( C - A ) ) <_ B ) ) $=
      ( cr wcel w3a cmin co caddc cicc cle wbr wa cabs cfv cxr 3adant3 rexr syl
      wb resubcl readdcl 3ad2ant3 elicc4 syl3anc absdifle 3coml bitr4d ) ADEZBD
      EZCDEZFZCABGHZABIHZJHEZUMCKLCUNKLMZCAGHNOBKLZULUMPEZUNPEZCPEZUOUPTULUMDEZ
      URUIUJVAUKABUAQUMRSULUNDEZUSUIUJVBUKABUBQUNRSUKUIUTUJCRUCUMUNCUDUEUKUIUJU
      QUPTCABUFUGUH $.
      $( [16-Nov-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Liouville's approximation theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d F a $.  $d X a $.  $d Y a $.  $d ph a $.
    aalioulem1.a $e |- ( ph -> F e. ( Poly ` ZZ ) ) $.
    aalioulem1.b $e |- ( ph -> X e. ZZ ) $.
    aalioulem1.c $e |- ( ph -> Y e. NN ) $.
    $( Lemma for ~ aaliou .  An integer polynomial cannot inflate the
       denominator of a rational by more than its degree. $)
    aalioulem1 $p |- ( ph -> ( ( F ` ( X / Y ) ) x. ( Y ^ ( deg ` F ) ) )
        e. ZZ ) $=
      ( va co cfv cexp cmul cc0 cz wcel cc wceq syl syl2anc cn0 cdiv cfz cv csu
      cdgr ccoe cply wne zcn nncn nnne0 divcl syl3anc coeid2 oveq1d fzfid dgrcl
      cn expcl wa zsscn wf 0z coef2 sylancl elfznn0 ffvelrn syl2an sseldi mulcl
      eqid fsummulc1 eqtrd adantr mulass adantl expdiv syl121anc nnexpcl nn0ssz
      div13 cmin elfzelz expsub syl22anc nnz fvex fznn0sub mpan zexpcl eqeltrrd
      cvv zmulcl eqeltrd fsumzcl ) ACDUAIZBJZDBUEJZKIZLIZMWRUBIZHUCZBUFJZJZWPXB
      KIZLIZWSLIZHUDZNAWTXAXFHUDZWSLIXHAWQXIWSLABNUGJOZWPPOZWQXIQEACPOZDPOZDMUH
      ZXKACNOZXLFCUIRADUROZXMGDUJRZAXPXNGDUKRZCDULUMZXCNHBWRWPXCVKZWRVKUNSUOAXA
      XFWSHAMWRUPZAXMWRTOZWSPOZXQAXJYBENBUQRZDWRUSZSAXBXAOZUTZXDPOZXEPOZXFPOYGN
      PXDVAATNXCVBZXBTOZXDNOZYFAXJMNOYJEVCXCNBXTVDVEXBWRVFZTNXBXCVGVHZVIZAXKYKY
      IYFXSYMWPXBUSVHZXDXEVJSVLVMAXAXGHYAYGXGXDXEWSLIZLIZNYGYHYIYCXGYRQYOYPYGXM
      YBYCAXMYFXQVNZAYBYFYDVNZYESZXDXEWSVOUMYGYLYQNOYRNOYNYGYQWSDXBKIZUAIZCXBKI
      ZLIZNYGYQUUDUUBUAIZWSLIZUUEYGXEUUFWSLYGXLXMXNYKXEUUFQYGNPCVAAXOYFFVNVIZYS
      AXNYFXRVNZYFYKAYMVPZCDXBVQVRUOYGUUDPOZUUBPOZUUBMUHZYCUUGUUEQYGXLYKUUKUUHU
      UJCXBUSSYGUUBUROZUULAXPYKUUNYFGYMDXBVSVHZUUBUJRYGUUNUUMUUOUUBUKRUUAUUDUUB
      WSWAVRVMYGUUCNOUUDNOZUUENOYGDWRXBWBIZKIZUUCNYGXMXNWRNOXBNOZUURUUCQYSUUIYG
      TNWRVTYTVIYFUUSAXBMWRWCVPDWRXBWDWEYGDNOZUUQTOZUURNOYGXPUUTAXPYFGVNDWFRYFU
      VAAWRWLOYFUVABUEWGWLXBMWRWHWIVPDUUQWJSWKAXOYKUUPYFFYMCXBWJVHUUCUUDWMSWNXD
      YQWMSWNWOWN $.
      $( [12-Nov-2014] $)
  $}

  ${
    $d ph x p q r a b c d $.  $d A x p q r a b c d $.  $d F x p q r a b c d $.
    aalioulem2.a $e |- N = ( deg ` F ) $.
    aalioulem2.b $e |- ( ph -> F e. ( Poly ` ZZ ) ) $.
    aalioulem2.c $e |- ( ph -> N e. NN ) $.
    aalioulem2.d $e |- ( ph -> A e. RR ) $.
    $( Lemma for ~ aaliou . $)
    aalioulem2 $p |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN (
        ( F ` ( p / q ) ) = 0 -> ( A = ( p / q ) \/
          ( x / ( q ^ N ) ) <_ ( abs ` ( A - ( p / q ) ) ) ) ) ) $=
      ( cc0 wceq cle crp cr c1 wcel wa syl vr va vb vc vd cv cdiv cfv cmin cabs
      co wbr wo wi cn wral cz wrex cexp csn ccnv cima crab cun clt csup wss 1rp
      snssi ax-mp ssrab2 unssi wor cfn c0 wne ltso cnvso mpbi a1i snfi cab cdgr
      chash cply c0p nnne0 eqcomi dgr0 3netr4g necon3i eqid fta1 syl2anc simpld
      fveq2 abrexfi cin dfrab2 inss1 eqsstri ssfi sylancl unfi sylancr 1re snid
      elexi elun1 ne0i mp2b rpssre sstri fisup2g syl13anc sseldi wn rpge0 breq1
      0re ralbidv rcla4ev reximi cc ad2antrr simplr resubcl recnd wb 3syl oveq2
      cvv fveq2d syl3anc ex rpre adantr elrp sylib ralimdva mp2an ssralv subeq0
      rgen necon3abid biimprd impr absrpcl wfn wf ffn fniniseg simprl mpbir2and
      plyf weq eqeq2d eqeq1 rexbidv elrab sylanbrc elun2 infmrlb expr ralrimiva
      orbi2d imbi2d cq znq qre eqeq1d eqeq2 breq2d orbi12d imbi12d rcla4v com12
      orrd ralrimivv cn0 simprr nnnn0 nnexpcl nnrp rpdivcl simpllr adantl abscl
      rpcnne0 divid nnge1 eqbrtrd ad2antlr lediv23 mpbid orim2d imim2d reximdva
      simpr letrd anassrs mpd ) AGUFZFUFZUGUKZDUHZLMZCUXEMZBUFZCUXEUIUKZUJUHZNU
      LZUMZUNZFUOUPZGUQUPZBOURZUXGUXHUXIUXDEUSUKZUGUKZUXKNULZUMZUNZFUOUPZGUQUPZ
      BOURAUAUFZDUHZLMZCUYEMZUXICUYEUIUKZUJUHZNULZUMZUNZUAPUPZBOURZUXQAQUTZUBUF
      ZCUCUFZUIUKZUJUHZMZUCDVALUTVBZURZUBOVCZVDZPVEVAZVFZORUYGUYHVUGUYJNULZUMZU
      NZUAPUPZUYOAVUEOVUGUYPVUDOQORUYPOVGVHQOVIVJVUCUBOVKVLZAPVUFVMZVUEVNRZVUEV
      OVPZVUEPVGZVUGVUERVUMAPVEVMVUMVQPVEVRVSVTAUYPVNRVUDVNRZVUNQWAAVUCUBWBZVNR
      ZVUDVURVGVUQAVUBVNRZVUSAVUTVUBWDUHDWCUHZNULZADUQWEUHRZDWFVPZVUTVVBSIAVVAW
      FWCUHZVPVVDAELVVAVVEAEUORZELVPJEWGTEVVAHWHWIWJDWFVVAVVEDWFWCWPWKTVUBUQDVU
      BWLWMWNWOUCUBVUBUYTWQTVUDVUROWRVURVUCUBOWSVUROWTXAVURVUDXBXCUYPVUDXDXEVUO
      AQUYPRQVUERVUOQQPXFXHXGQUYPVUDXIVUEQXJXKVTVUPAVUEOPVULXLXMZVTPVUEVUFXNXOX
      PAVUJUAPAUYEPRZSZUYGVUIVVIUYGSZUYHVUHVVIUYGUYHXQZVUHVVIUYGVVKSZSZVUPUDUFZ
      UEUFZNULZUEVUEUPZUDPURZUYJVUERZVUHVUPVVMVVGVTVVRVVMVVPUEOUPZUDPURZVVRLPRL
      VVONULZUEOUPZVWAXTVWBUEOVVOXRUUDVVTVWCUDLPVVNLMVVPVWBUEOVVNLVVONXSYAYBUUA
      VVTVVQUDPVUEOVGVVTVVQUNVULVVPUEVUEOUUBVJYCVJVTVVMUYJVUDRZVVSVVMUYJORZUYJU
      YTMZUCVUBURZVWDVVMUYIYDRUYILVPZVWEVVMUYIVVMCPRZVVHUYIPRAVWIVVHVVLKYEAVVHV
      VLYFZCUYEYGWNYHVVIUYGVVKVWHVVJVWHVVKVVJUYHUYILVVJCYDRUYEYDRZUYILMUYHYIVVJ
      CAVWIVVHUYGKYEYHVVJUYEAVVHUYGYFYHCUYEUUCWNUUEUUFUUGUYIUUHWNVVMUYEVUBRZUYJ
      UYJMZVWGVVMVWLVWKUYGVVMDYDUUIZLYLRVWLVWKUYGSYIAVWNVVHVVLAVVCYDYDDUUJVWNIU
      QDUUOYDYDDUUKYJYELPXTXHYDLUYEDYLUULXCVVMUYEVWJYHVVIUYGVVKUUMUUNUYJWLVWFVW
      MUCUYEVUBUCUAUUPZUYTUYJUYJVWOUYSUYIUJUYRUYECUIYKYMUUQYBXCVUCVWGUBUYJOUYQU
      YJMVUAVWFUCVUBUYQUYJUYTUURUUSUUTUVAUYJVUDUYPUVBTUDUEUYJVUEUVCYNUVDUVRYOUV
      EUYNVUKBVUGOUXIVUGMZUYMVUJUAPVWPUYLVUIUYGVWPUYKVUHUYHUXIVUGUYJNXSUVFUVGYA
      YBWNUYNUXPBOUYNUXNGFUQUOUXCUQRZUXDUORZSZUYNUXNVWSUXEPRZUYNUXNUNVWSUXEUVHR
      VWTUXCUXDUVIUXEUVJTZUYMUXNUAUXEPUYEUXEMZUYGUXGUYLUXMVXBUYFUXFLUYEUXEDWPUV
      KVXBUYHUXHUYKUXLUYEUXECUVLVXBUYJUXKUXINVXBUYIUXJUJUYEUXECUIYKYMUVMUVNUVOU
      VPTUVQUVSYCTAUXPUYDBOAUXIORZSZUXOUYCGUQVXDVWQSUXNUYBFUOVXDVWQVWRUXNUYBUNV
      XDVWSSZUXMUYAUXGVXEUXLUXTUXHVXEUXLUXTVXEUXLSZUXSUXIUXKVXEUXSPRZUXLVXEUXSO
      RZVXGVXEVXCUXRORZVXHAVXCVWSYFZVXEUXRUORZVXIVXEVWREUVTRZVXKVXDVWQVWRUWAAVX
      LVXCVWSAVVFVXLJEUWBTYEUXDEUWCWNZUXRUWDTZUXIUXRUWEWNUXSYPTYQVXFVXCUXIPRZAV
      XCVWSUXLUWFUXIYPZTVXEUXKPRZUXLVXEUXJYDRVXQVXEUXJVXEVWIVWTUXJPRAVWIVXCVWSK
      YEVWSVWTVXDVXAUWGCUXEYGWNYHUXJUWHTYQVXEUXSUXINULZUXLVXEUXIUXIUGUKZUXRNULZ
      VXRVXEVXSQUXRNVXEVXCUXIYDRUXILVPSVXSQMVXJUXIUWIUXIUWJYJVXEVXKQUXRNULVXMUX
      RUWKTUWLVXEVXOVXOLUXIVEULSZUXRPRLUXRVEULSZVXTVXRYIVXCVXOAVWSVXPUWMVXEVXCV
      YAVXJUXIYRYSVXEVXIVYBVXNUXRYRYSUXIUXIUXRUWNYNUWOYQVXEUXLUWSUWTYOUWPUWQUXA
      YTYTUWRUXB $.
      $( [15-Nov-2014] $)

    aalioulem3.e $e |- ( ph -> ( F ` A ) = 0 ) $.
    $( Lemma for ~ aaliou . $)
    aalioulem3 $p |- ( ph -> E. x e. RR+ A. r e. RR ( ( abs ` ( A - r ) ) <_ 1
        -> ( x x. ( abs ` ( F ` r ) ) ) <_ ( abs ` ( A - r ) ) ) ) $=
      ( co cfv c1 cle wbr cr wcel cc cc0 va vc vb cv cmin cabs cmul wi wral crp
      wrex caddc cicc 1re resubcl sylancl peano2re syl ccpnNEW crn cint wss cn0
      cres wfn fncpn 1nn0 fnfvelrn mp2an intss1 ax-mp cply plycpn sseldi df-ima
      cz cima wf zssre ax-resscn plyss sseli plyreres 3syl frn syl5eqss iccssre
      cdm syl2anc syl6ss wceq plyf fdm sseqtr4d c1lip3 w3a simp2 recnd 3ad2ant1
      wa adantr abssub simp3 eqbrtrd wb a1i elicc4abs syl3anc mpbird subid abs0
      fveq2d nn0ge0i eqbrtri syl6eqbr fveq2 oveq2d oveq2 breq12d oveq1d rcla42v
      weq oveq1 simp1l 0cn syl6eqel ffvelrn subid1 eqtrd breq1d mpd cdiv adantl
      wne ad2antrr abscl absge0 syl5ibrcom expimpd remulcl sylibd 3exp ralrimdv
      com34 com23 reximdva cif 1rp wn recn df-ne biimpri absrpcl syl2an rpreccl
      ifclda wo eqid eqif mpbi simprl 0re letri3 simplrr mul02 mpbir2and ax-1cn
      breqtrd mul01i syl6eq simpllr sylancom rpcnne0 divrec2 3expb simplr leabs
      simprr jca ad2antlr lemul1a syl31anc letrd clt ledivmul eqbrtrrd sylan2br
      elrp sylib jaod mpi expr imim2d ralimdva imbi2d ralbidv rcla4ev rexlimdva
      ee12an ) ACFUDZUELZUFMZNOPZUWTDMZUFMZUAUDZUXBUGLZOPZUHZFQUIZUAQUKZUXCBUDZ
      UXEUGLZUXBOPZUHZFQUIZBUJUKZAUBUDZDMZUCUDZDMZUELZUFMZUXFUXRUXTUELZUFMZUGLZ
      OPZUBCNUELZCNULLZUMLZUIUCUYJUIZUAQUKUXKAUCUBUYHUYIUADACQRZNQRZUYHQRZJUNCN
      UOUPZAUYLUYIQRZJCUQURZAUSUTZVAZNUSMZDQVDZUYTUYRRZUYSUYTVBUSVCVENVCRVUBVFV
      GVCNUSVHVIUYTUYRVJVKADVPVLMZRZVUAUYSRHVPDVMURVNADQVQVUAUTZQDQVOAQQVUAVRZV
      UEQVBAVUDDQVLMZRVUFHVUCVUGDVPQVBQSVBVUCVUGVBVSVTVPQWAVIWBDWCWDQQVUAWEURWF
      AUYJSDWHZAUYJQSAUYNUYPUYJQVBUYOUYQUYHUYIWGWIVTWJASSDVRZVUHSWKAVUDVUIHVPDW
      LURZSSDWMURWNWOAUYKUXJUAQAUXFQRZWTZUYKUXIFQVULUWTQRZUYKUXIVULVUMUXCUYKUXH
      VULVUMUXCUYKUXHUHVULVUMUXCWPZUYKCDMZUXDUELZUFMZUXGOPZUXHVUNUWTUYJRZCUYJRZ
      UYKVURUHVUNVUSUWTCUELUFMZNOPZVUNVVAUXBNOVUNUWTSRZCSRZVVAUXBWKVUNUWTVULVUM
      UXCWQZWRZVUNCVULVUMUYLUXCAUYLVUKJXAWSZWRUWTCXBWIVULVUMUXCXCXDVUNUYLUYMVUM
      VUSVVBXEVVGUYMVUNUNXFVVECNUWTXGXHXIVULVUMVUTUXCAVUTVUKAVUTCCUELZUFMZNOPZA
      VVITUFMZNOAVVHTUFAVVDVVHTWKACJWRCXJURXLVVKTNOXKNVGXMXNXOAUYLUYMUYLVUTVVJX
      EJUYMAUNXFJCNCXGXHXIXAWSUYGVURUXSUXDUELZUFMZUXFUXRUWTUELZUFMZUGLZOPUCUBUW
      TCUYJUYJUCFYBZUYCVVMUYFVVPOVVQUYBVVLUFVVQUYAUXDUXSUEUXTUWTDXPXQXLVVQUYEVV
      OUXFUGVVQUYDVVNUFUXTUWTUXRUEXRXLXQXSUXRCWKZVVMVUQVVPUXGOVVRVVLVUPUFVVRUXS
      VUOUXDUEUXRCDXPXTXLVVRVVOUXBUXFUGVVRVVNUXAUFUXRCUWTUEYCXLXQXSYAWIVUNVUQUX
      EUXGOVUNVUQUXDVUOUELZUFMZUXEVUNVUOSRUXDSRZVUQVVTWKVUNVUOTSVUNAVUOTWKAVUKV
      UMUXCYDKURZYEYFVUNVUIVVCVWAVULVUMVUIUXCAVUIVUKVUJXAWSVVFSSUWTDYGZWIZVUOUX
      DXBWIVUNVVSUXDUFVUNVVSUXDTUELZUXDVUNVUOTUXDUEVWBXQVUNVWAVWEUXDWKVWDUXDYHU
      RYIXLYIYJUUAUUBUUDUUEUUCUUFYKAUXJUXQUAQVULUXFTWKZNNUXFUFMZYLLZUUGZUJRUXJU
      XCVWIUXEUGLZUXBOPZUHZFQUIZUXQVULVWFNVWHUJNUJRVULVWFWTUUHXFVULVWFUUIZWTVWG
      UJRZVWHUJRVULUXFSRZUXFTYNZVWOVWNVUKVWPAUXFUUJYMVWQVWNUXFTUUKZUULUXFUUMZUU
      NVWGUUOURUUPVULUXIVWLFQVULVUMWTUXHVWKUXCVULVUMUXHVWKVULVUMUXHWTZWTZVWFVWI
      NWKZWTZVWNVWIVWHWKZWTZUUQZVWKVWIVWIWKVXFVWIUURVWFVWINVWHUUSUUTVXAVXCVWKVX
      EVXAVWFVXBVWKVXAVWFWTZVWKVXBNUXEUGLZUXBOPVXGVXHTUXBOVXGVXHNTUGLTVXGUXETNU
      GVXGUXETWKZUXETOPZTUXEOPZVXGUXEQRZTQRVXIVXJVXKWTXEVXAVXLVWFVXAVWAVXLVXAVU
      IVVCVWAAVUIVUKVWTVUJYOVXAUWTVULVUMUXHUVAZWRVWCWIZUXDYPURZXAUVBUXETUVCUPVX
      GUXEUXGTOVULVUMUXHVWFUVDVXGUXGTUXBUGLZTVWFUXGVXPWKVXAUXFTUXBUGYCYMVXGUXBS
      RZVXPTWKVXAVXQVWFVXAUXBVXAUXASRZUXBQRZVXAUXAVXAUYLVUMUXAQRAUYLVUKVWTJYOVX
      MCUWTUOWIWRZUXAYPURZWRXAUXBUVEURYIUVHVXGVWAVXKVXAVWAVWFVXNXAUXDYQURUVFXQN
      UVGUVIUVJVXGVXRTUXBOPZVXAVXRVWFVXTXAUXAYQZURXDVXBVWJVXHUXBOVWINUXEUGYCYJY
      RYSVXAVWNVXDVWKVXAVWNWTVWKVXDVWHUXEUGLZUXBOPZVWNVXAVWQVYEVWRVXAVWQWTZUXEV
      WGYLLZVYDUXBOVYFUXESRZVWGSRZVWGTYNZWTZVYGVYDWKZVYFUXEVXAVXLVWQVXOXAZWRVYF
      VWOVYKVXAVWQVWPVWOVYFUXFAVUKVWTVWQUVKWRVWSUVLZVWGUVMURVYHVYIVYJVYLUXEVWGU
      VNUVOWIVYFVYGUXBOPZUXEVWGUXBUGLZOPZVXAVYQVWQVXAUXEUXGVYPVXOVXAVUKVXSUXGQR
      AVUKVWTUVPZVYAUXFUXBYTWIVXAVWGQRZVXSVYPQRVXAVWPVYSVXAUXFVYRWRUXFYPURZVYAV
      WGUXBYTWIVULVUMUXHUVRVXAVUKVYSVXSVYBWTUXFVWGOPZUXGVYPOPVYRVYTVXAVXSVYBVYA
      VXAVXRVYBVXTVYCURUVSVUKWUAAVWTUXFUVQUVTUXFVWGUXBUWAUWBUWCXAVYFVXLVXSVYSTV
      WGUWDPWTZVYOVYQXEVYMVXAVXSVWQVYAXAVYFVWOWUBVYNVWGUWHUWIUXEUXBVWGUWEXHXIUW
      FUWGVXDVWJVYDUXBOVWIVWHUXEUGYCYJYRYSUWJUWKUWLUWMUWNUXPVWMBVWIUJUXLVWIWKZU
      XOVWLFQWUCUXNVWKUXCWUCUXMVWJUXBOUXLVWIUXEUGYCYJUWOUWPUWQUWSUWRYK $.
      $( [15-Nov-2014] $)

    $( Lemma for ~ aaliou . $)
    aalioulem4 $p |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN (
        ( ( F ` ( p / q ) ) =/= 0 /\ ( abs ` ( A - ( p / q ) ) ) <_ 1 ) ->
          ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_
            ( abs ` ( A - ( p / q ) ) ) ) ) ) $=
      ( co cfv cle wbr cmul cr wcel syl va cv cmin cabs c1 wi wral crp wrex cc0
      cdiv wne wa wceq wo cn cz aalioulem3 w3a cq simp2l simp2r znq syl2anc qre
      cexp simp3r oveq2 fveq2d breq1d fveq2 oveq2d breq12d imbi12d rcla4v com23
      sylc simp1r nnrp simp1l nnz 3syl rpexpcl rpdivcl rpre adantr cc cply plyf
      recnd ffvelrn abscl remulcl resubcl rpcn rpne0 divrec syl3anc rpge0 absid
      wf absmul oveq1d eqtrd cdgr mulcom oveq2i syl6eq aalioulem1 simp3l mulne0
      eqeltrd syl22anc nnabscl eqeltrrd nnge1 clt 1re a1i sylib ledivmul mpbird
      wb elrp rpreccl lemul2 mpbid eqbrtrd simpr letrd olcd syld 3exp ralrimdvv
      ex com34 reximdva mpd ) ACUAUBZUCMZUDNZUEOPZBUBZYSDNZUDNZQMZUUAOPZUFZUARU
      GZBUHUIGUBZFUBZUKMZDNZUJULZCUULUCMZUDNZUEOPZUMZCUULUNZUUCUUKEVFMZUKMZUUPO
      PZUOZUFZFUPUGGUQUGZBUHUIABCDEUAHIJKLURAUUIUVEBUHAUUCUHSZUMZUUIUVDGFUQUPUV
      GUUJUQSZUUKUPSZUMZUUIUVDUVGUVJUURUUIUVCUVGUVJUURUUIUVCUFUVGUVJUURUSZUUIUU
      CUUMUDNZQMZUUPOPZUVCUVKUULRSZUUQUUIUVNUFUVKUULUTSZUVOUVKUVHUVIUVPUVGUVHUV
      IUURVAZUVGUVHUVIUURVBZUUJUUKVCVDUULVETZUVGUVJUUNUUQVGUVOUUIUUQUVNUUHUUQUV
      NUFUAUULRYSUULUNZUUBUUQUUGUVNUVTUUAUUPUEOUVTYTUUOUDYSUULCUCVHVIZVJUVTUUFU
      VMUUAUUPOUVTUUEUVLUUCQUVTUUDUUMUDYSUULDVKVIVLUWAVMVNVOVPVQUVKUVNUVCUVKUVN
      UMZUVBUUSUWBUVAUVMUUPUVKUVARSZUVNUVKUVAUHSZUWCUVKUVFUUTUHSZUWDAUVFUVJUURV
      RZUVKUUKUHSZEUQSZUWEUVKUVIUWGUVRUUKVSTUVKAEUPSUWHAUVFUVJUURVTZJEWAWBUUKEW
      CVDZUUCUUTWDVDUVAWETWFUVKUVMRSZUVNUVKUUCRSZUVLRSZUWKUVKUVFUWLUWFUUCWETUVK
      UUMWGSZUWMUVKWGWGDXAZUULWGSUWNUVKADUQWHNSZUWOUWIIUQDWIWBUVKUULUVSWJWGWGUU
      LDWKVDZUUMWLTZUUCUVLWMVDWFUVKUUPRSZUVNUVKUUOWGSUWSUVKUUOUVKCRSZUVOUUORSUV
      KAUWTUWIKTUVSCUULWNVDWJUUOWLTWFUVKUVAUVMOPUVNUVKUVAUUCUEUUTUKMZQMZUVMOUVK
      UUCWGSZUUTWGSZUUTUJULZUVAUXBUNUVKUVFUXCUWFUUCWOTUVKUWEUXDUWJUUTWOTZUVKUWE
      UXEUWJUUTWPTZUUCUUTWQWRUVKUXAUVLOPZUXBUVMOPZUVKUXHUEUUTUVLQMZOPZUVKUXJUPS
      UXKUVKUUTUUMQMZUDNZUXJUPUVKUXMUUTUDNZUVLQMZUXJUVKUXDUWNUXMUXOUNUXFUWQUUTU
      UMXBVDUVKUXNUUTUVLQUVKUUTRSZUJUUTOPZUXNUUTUNUVKUWEUXPUWJUUTWETUVKUWEUXQUW
      JUUTWSTUUTWTVDXCXDUVKUXLUQSUXLUJULZUXMUPSUVKUXLUUMUUKDXENZVFMZQMZUQUVKUXL
      UUMUUTQMZUYAUVKUXDUWNUXLUYBUNUXFUWQUUTUUMXFVDUUTUXTUUMQEUXSUUKVFHXGXGXHUV
      KDUUJUUKUVKAUWPUWIITUVQUVRXIXLUVKUXDUXEUWNUUNUXRUXFUXGUWQUVGUVJUUNUUQXJUU
      TUUMXKXMUXLXNVDXOUXJXPTUVKUERSZUWMUXPUJUUTXQPUMZUXHUXKYCUYCUVKXRXSUWRUVKU
      WEUYDUWJUUTYDXTUEUVLUUTYAWRYBUVKUXARSZUWMUWLUJUUCXQPUMZUXHUXIYCUVKUWEUXAU
      HSUYEUWJUUTYEUXAWEWBUWRUVKUVFUYFUWFUUCYDXTUXAUVLUUCYFWRYGYHWFUVKUVNYIYJYK
      YOYLYMYPVPYNYQYR $.
      $( [16-Nov-2014] $)

    $d N a b x $.

    $( Lemma for ~ aaliou . $)
    aalioulem5 $p |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN (
        ( F ` ( p / q ) ) =/= 0 -> ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_
            ( abs ` ( A - ( p / q ) ) ) ) ) ) $=
      ( c1 cle wbr wa crp wcel cr syl va cv cdiv co cfv cc0 cmin cabs wceq cexp
      wne wo wi cn wral cz wrex aalioulem4 cif simpr 1rp a1i syl2anc clt adantr
      ifcl w3a simprr nnrp ad2antrr nnz rpexpcl rpdivcl rpre 1re znq qre adantl
      cc cq resubcl recnd abscl 3jca rpreccl simplr min2 wb elrp lediv1 syl3anc
      sylib mpbid cmul cn0 nnnn0 nnexpcl 1nn nnmulcl nnge1 ledivmul mpbird ltle
      letrd sylancr imp jca letr sylc olcd pm3.21 min1 anim1i ex orim2d imim12d
      pm2.61ltlei anassrs ralimdva breq1d orbi2d imbi2d 2ralbidv rcla4ev ee12an
      a1d oveq1 rexlimdva mpd ) AGUBZFUBZUCUDZDUEUFUKZCYLUGUDZUHUEZMNOZPZCYLUIZ
      UAUBZYKEUJUDZUCUDZYONOZULZUMZFUNUOZGUPUOZUAQUQYMYRBUBZYTUCUDZYONOZULZUMZF
      UNUOGUPUOZBQUQZAUACDEFGHIJKLURAUUFUUMUAQAYSQRZPZYSMNOZYSMUSZQRZUUFYMYRUUQ
      YTUCUDZYONOZULZUMZFUNUOZGUPUOZUUMUUOUUNMQRZUURAUUNUTUVEUUOVAVBUUPYSMQVFVC
      ZUUOUUEUVCGUPUUOYJUPRZPUUDUVBFUNUUOUVGYKUNRZUUDUVBUMZUUOUVGUVHPZPZUVIMYOU
      VKMYOVDOZPZUVBUUDUVMUVAYMUVMUUTYRUVMUUSSRZMSRZYOSRZVGZUUSMNOZMYONOZPUUTUV
      KUVQUVLUVKUVNUVOUVPUVKUUSQRZUVNUVKUURYTQRZUVTUUOUURUVJUVFVEZUVKYKQRZEUPRZ
      UWAUVKUVHUWCUUOUVGUVHVHZYKVITUVKEUNRZUWDAUWFUUNUVJJVJZEVKTYKEVLVCZUUQYTVM
      VCUUSVNTZUVOUVKVOVBZUVKYNVSRUVPUVKYNUVKCSRZYLSRZYNSRAUWKUUNUVJKVJUVJUWLUU
      OUVJYLVTRUWLYJYKVPYLVQTVRCYLWAVCWBYNWCTZWDVEUVMUVRUVSUVKUVRUVLUVKUUSMYTUC
      UDZMUWIUVKUWNQRZUWNSRUVKUWAUWOUWHYTWETUWNVNTUWJUVKUUQMNOZUUSUWNNOZUVKYSSR
      ZUVOUWPUVKUUNUWRAUUNUVJWFZYSVNTZUWJYSMWGVCUVKUUQSRZUVOYTSRUFYTVDOPZUWPUWQ
      WHUVKUURUXAUWBUUQVNTZUWJUVKUWAUXBUWHYTWIWLZUUQMYTWJWKWMUVKUWNMNOZMYTMWNUD
      ZNOZUVKUXFUNRZUXGUVKYTUNRZMUNRZUXHUVKUVHEWORZUXIUWEUVKUWFUXKUWGEWPTYKEWQV
      CUXJUVKWRVBYTMWSVCUXFWTTUVKUVOUVOUXBUXEUXGWHUWJUWJUXDMMYTXAWKXBXDVEUVKUVL
      UVSUVKUVOUVPUVLUVSUMVOUWMMYOXCXEXFXGUUSMYOXHXIXJYFYFUVKYPPZYMYQUUCUVAYPYM
      YQUMUVKYPYMXKVRUXLUUBUUTYRUVKUUBUUTUMYPUVKUUBUUTUVKUUBPUVNUUASRZUVPVGZUUS
      UUANOZUUBPUUTUVKUXNUUBUVKUVNUXMUVPUWIUVKUUAQRZUXMUVKUUNUWAUXPUWSUWHYSYTVM
      VCUUAVNTUWMWDVEUVKUXOUUBUVKUUQYSNOZUXOUVKUWRUVOUXQUWTUWJYSMXLVCUVKUXAUWRU
      XBUXQUXOWHUXCUWTUXDUUQYSYTWJWKWMXMUUSUUAYOXHXIXNVEXOXPUWJUWMXQXRXSXSUULUV
      DBUUQQUUGUUQUIZUUKUVBGFUPUNUXRUUJUVAYMUXRUUIUUTYRUXRUUHUUSYONUUGUUQYTUCYG
      XTYAYBYCYDYEYHYI $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aaliou . $)
    aalioulem6 $p |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN
        ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_
          ( abs ` ( A - ( p / q ) ) ) ) ) $=
      ( cle wbr cn wral wa crp wcel cr va vb cv cdiv co cfv wceq cexp cmin cabs
      cc0 wo wi cz wne wrex aalioulem2 aalioulem5 reeanv sylanbrc r19.26-2 ifcl
      cif simpr w3a ad2antlr nnrp ad2antll ad2antrr nnz rpexpcl syl2anc rpdivcl
      adantl syl rpre simplrl cc cq znq qre resubcl recn abscl 3syl 3jca adantr
      simplrr min1 clt wb elrp sylib lediv1 syl3anc mpbid anim1i letr ex orim2d
      sylc embantd adantrd min2 adantld pm2.61dane ralimdva oveq1 breq1d orbi2d
      anassrs 2ralbidv rcla4ev ee12an syl5bir rexlimdvva mpd ) AGUCZFUCZUDUEZDU
      FZUKUGZCXTUGZUAUCZXSEUHUEZUDUEZCXTUIUEZUJUFZMNZULZUMZFOPGUNPZYAUKUOZYCUBU
      CZYEUDUEZYHMNZULZUMZFOPGUNPZQZUBRUPUARUPZYCBUCZYEUDUEZYHMNZULZFOPGUNPZBRU
      PZAYLUARUPYSUBRUPUUAAUACDEFGHIJKUQAUBCDEFGHIJKLURYLYSUAUBRRUSUTAYTUUGUAUB
      RRYTYKYRQZFOPZGUNPZAYDRSZYNRSZQZQZUUGYKYRGFUNOVAUUNYDYNMNZYDYNVCZRSZUUJYC
      UUPYEUDUEZYHMNZULZFOPZGUNPZUUGUUMUUQAUUOYDYNRVBZVNUUNUUIUVAGUNUUNXRUNSZQU
      UHUUTFOUUNUVDXSOSZUUHUUTUMZUUNUVDUVEQZQZUVFYAUKUVHYBQZYKUUTYRUVIYBYJUUTUV
      HYBVDUVIYIUUSYCUVHYIUUSUMYBUVHYIUUSUVHYIQUURTSZYFTSZYHTSZVEZUURYFMNZYIQUU
      SUVHUVMYIUVHUVJUVKUVLUVHUURRSZUVJUVHUUQYERSZUVOUUMUUQAUVGUVCVFZUVHXSRSZEU
      NSZUVPUVEUVRUUNUVDXSVGVHUVHEOSZUVSAUVTUUMUVGJVIEVJVOXSEVKVLZUUPYEVMVLUURV
      PVOZUVHYFRSZUVKUVHUUKUVPUWCAUUKUULUVGVQZUWAYDYEVMVLYFVPVOUVHYGTSZYGVRSUVL
      UVHCTSZXTTSZUWEAUWFUUMUVGKVIUVGUWGUUNUVGXTVSSUWGXRXSVTXTWAVOVNCXTWBVLYGWC
      YGWDWEZWFWGUVHUVNYIUVHUUPYDMNZUVNUVHYDTSZYNTSZUWIUVHUUKUWJUWDYDVPVOZUVHUU
      LUWKAUUKUULUVGWHZYNVPVOZYDYNWIVLUVHUUPTSZUWJYETSUKYEWJNQZUWIUVNWKUVHUUQUW
      OUVQUUPVPVOZUWLUVHUVPUWPUWAYEWLWMZUUPYDYEWNWOWPWQUURYFYHWRXAWSWGWTXBXCUVH
      YMQZYRUUTYKUWSYMYQUUTUVHYMVDUWSYPUUSYCUVHYPUUSUMYMUVHYPUUSUVHYPQUVJYOTSZU
      VLVEZUURYOMNZYPQUUSUVHUXAYPUVHUVJUWTUVLUWBUVHYORSZUWTUVHUULUVPUXCUWMUWAYN
      YEVMVLYOVPVOUWHWFWGUVHUXBYPUVHUUPYNMNZUXBUVHUWJUWKUXDUWLUWNYDYNXDVLUVHUWO
      UWKUWPUXDUXBWKUWQUWNUWRUUPYNYEWNWOWPWQUURYOYHWRXAWSWGWTXBXEXFXKXGXGUUFUVB
      BUUPRUUBUUPUGZUUEUUTGFUNOUXEUUDUUSYCUXEUUCUURYHMUUBUUPYEUDXHXIXJXLXMXNXOX
      PXQ $.
      $( [16-Nov-2014] $)

    $( Liouville's theorem on diophantine approximation:  Any algebraic number,
       being a root of a polynomial ` F ` in integer coefficients, is not
       approximable beyond order ` N = deg ( F ) ` by rational numbers.  In
       this form, it also applies to rational numbers themselves, which are not
       well approximable by other rational numbers. $)
    aaliou $p |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( A = ( p / q ) \/
      ( x / ( q ^ N ) ) < ( abs ` ( A - ( p / q ) ) ) ) ) $=
      ( cdiv co wbr cn cz crp wcel cr va cv wceq cexp cmin cabs cfv cle wo wral
      wrex clt aalioulem6 wa rphalfcl adantl w3a ad2antlr nnrp ad2antll nnz syl
      c2 wi ad2antrr rpexpcl syl2anc rpdivcl rpre simplr adantr znq qre resubcl
      cc cq syl2an recn abscl 3syl 3jca rphalflt cc0 wb elrp sylib ltdiv1 mpbid
      syl3anc anim1i ltletr sylsyld orim2d anassrs ralimdva oveq1 breq1d orbi2d
      ex 2ralbidv rcla4ev ee12an rexlimdva mpd ) ACGUBZFUBZMNZUCZUAUBZXFEUDNZMN
      ZCXGUENZUFUGZUHOZUIZFPUJZGQUJZUARUKXHBUBZXJMNZXMULOZUIZFPUJGQUJZBRUKZAUAC
      DEFGHIJKLUMAXQYCUARAXIRSZUNZXIVCMNZRSZXQXHYFXJMNZXMULOZUIZFPUJZGQUJZYCYDY
      GAXIUOZUPYEXPYKGQYEXEQSZUNXOYJFPYEYNXFPSZXOYJVDYEYNYOUNZUNZXNYIXHYQYHTSZX
      KTSZXMTSZUQXNYHXKULOZXNUNZYIYQYRYSYTYQYHRSZYRYQYGXJRSZUUCYDYGAYPYMURZYQXF
      RSZEQSZUUDYOUUFYEYNXFUSUTAUUGYDYPAEPSUUGJEVAVBVEXFEVFVGZYFXJVHVGYHVIVBYQX
      KRSZYSYQYDUUDUUIAYDYPVJUUHXIXJVHVGXKVIVBYQXLTSZXLVOSYTYECTSZXGTSZUUJYPAUU
      KYDKVKYPXGVPSUULXEXFVLXGVMVBCXGVNVQXLVRXLVSVTWAYQXNUUBYQUUAXNYQYFXIULOZUU
      AYDUUMAYPXIWBURYQYFTSZXITSZXJTSWCXJULOUNZUUMUUAWDYQYGUUNUUEYFVIVBYDUUOAYP
      XIVIURYQUUDUUPUUHXJWEWFYFXIXJWGWIWHWJWSYHXKXMWKWLWMWNWOWOYBYLBYFRXRYFUCZY
      AYJGFQPUUQXTYIXHUUQXSYHXMULXRYFXJMWPWQWRWTXAXBXCXD $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d ph k a b c d $.  $d A k a b c d $.  $d B k a b c d $.  $d C k a b c d $.
    $d F a b c d $.
    geolim3.a $e |- ( ph -> A e. ZZ ) $.
    geolim3.b1 $e |- ( ph -> B e. CC ) $.
    geolim3.b2 $e |- ( ph -> ( abs ` B ) < 1 ) $.
    geolim3.c $e |- ( ph -> C e. CC ) $.
    geolim3.f $e |- F = ( k e. ( ZZ>= ` A ) |-> ( C x. ( B ^ ( k - A ) ) ) ) $.
    $( Geometric series convergence with arbitrary shift, radix, and
       multiplicative constant. $)
    geolim3 $p |- ( ph -> seq A ( + , F ) ~~> ( C / ( 1 - B ) ) ) $=
      ( caddc co cexp cmul c1 wceq cc0 wcel cc va cseq cuz cfv cv cmin cmpt cli
      cdiv seqeq3 ax-mp wbr cneg cshi cn0 cvv nn0uz cz 0z ovex oveq2 eqid fvmpt
      a1i adantl geolim expcl sylan eqeltrd zcn syl nn0cn mptex shftval4 syl2an
      wa fvex uzaddcl oveq1 oveq2d pncan2 eqtr4d 3eqtrd isermulc2 negid seqeq1d
      uzid wne ax-1cn subcl sylancr cabs cle 1re 1nn0 nn0ge0i absid mp2an abscl
      cr clt ltne syl3anc eqnetrd fveq2 necon3i subeq0 necon3bid mpbird 3brtr4d
      wb divrec znegcl isershft syl5eqbr ) ALFBUBZLEBUCUDZDCEUEZBUFMZNMZOMZUGZB
      UBZDPCUFMZUIMZUHFYBQXPYCQKLFYBBUJUKAYCYEUHULZLYBBUMZUNMZBYGLMZUBZYEUHULZA
      LYHRUBDPYDUIMZOMZYJYEUHAYLDUAEUOCXRNMZUGZYHRUPUOUQRURSAUSVDYLUPSAPYDUIUTV
      DJACUAYOHIUAUEZUOSZYPYOUDZCYPNMZQAEYPYNYSUOYOXRYPCNVAYOVBCYPNUTVCVEZVFAYQ
      VPZYRYSTYTACTSZYQYSTSHCYPVGVHVIUUAYPYHUDZBYPLMZYBUDZDCUUDBUFMZNMZOMZDYROM
      ABTSZYPTSZUUCUUEQYQABURSZUUIGBVJVKZYPVLZBYPYBEXQYABUCVQVMZVNVOUUAUUDXQSZU
      UEUUHQABXQSZYQUUOAUUKUUPGBWGVKYPBBVRVHEUUDYAUUHXQYBXRUUDQZXTUUGDOUUQXSUUF
      CNXRUUDBUFVSVTVTYBVBDUUGOUTVCVKUUAUUGYRDOUUAUUGYSYRUUAUUFYPCNAUUIUUJUUFYP
      QYQUULUUMBYPWAVOVTYTWBVTWCWDAYIRLYHAUUIYIRQUULBWEVKWFADTSYDTSZYDRWHZYEYMQ
      JAPTSZUUBUURWIHPCWJWKAUUSPCWHZAPWLUDZCWLUDZWHUVAAUVBPUVCUVBPQZAPWTSZRPWMU
      LUVDWNPWOWPPWQWRVDAUVCWTSZUVEUVCPXAULPUVCWHAUUBUVFHCWSVKUVEAWNVDIUVCPXBXC
      XDPCUVBUVCPCWLXEXFVKAYDRPCAUUTUUBYDRQPCQXKWIHPCXGWKXHXIDYDXLXCXJAUUKYGURS
      ZYEUPSZYFYKXKGAUUKUVGGBXMVKUVHADYDUIUTVDYELYBBYGUPUUNXNXCXIXO $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d A a k x p q $.

    $( Liouville's approximation theorem for algebraic numbers per se. $)
    aaliou2 $p |- ( A e. ( AA i^i RR ) -> E. k e. NN E. x e. RR+ A. p e. ZZ
        A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ k ) ) <
            ( abs ` ( A - ( p / q ) ) ) ) ) $=
      ( va caa wcel cv cdiv co wceq cfv cn wral cz wrex cc cc0 c0p cr cexp cmin
      cin wa cabs clt wbr wo crp elin cply csn cdif wi elaa w3a cdgr cxp eldifn
      wn 3ad2ant1 simpr fveq1 adantl simpl2 simpl3 recnd fvex fvconst2 3eqtr3rd
      sneqd xpeq2d eqtrd df-0p syl6eqr elsn sylibr mtand wb eldifi 0dgrb mtbird
      syl cn0 dgrcl elnn0 sylib orel2 sylc eqid simp3 simp2 aaliou oveq2 oveq2d
      breq1d orbi2d 2ralbidv rexbidv rcla4ev syl2anc 3exp rexlimiv sylbi imp )
      BGUAUDHBGHZBUAHZUEBEIDIZJKZLZAIZXICIZUBKZJKZBXJUCKUFMZUGUHZUIZDNOEPOZAUJQ
      ZCNQZBGUAUKXGXHYAXGBRHZBFIZMZSLZFPULMZTUMZUNZQZUEXHYAUOZBFUPYIYJYBYEYJFYH
      YCYHHZYEXHYAYKYEXHUQZYCURMZNHZXKXLXIYMUBKZJKZXPUGUHZUIZDNOEPOZAUJQZYAYLYM
      SLZVAYNUUAUIZYNYLUUAYCRSYCMZUMZUSZLZYLUUFYCYGHZYKYEUUGVAXHYCYFYGUTVBYLUUF
      UEZYCTLUUGUUHYCRSUMZUSZTUUHYCUUEUUJYLUUFVCUUHUUDUUIRUUHUUCSUUHYDBUUEMZSUU
      CUUFYDUUKLYLBYCUUEVDVEYKYEXHUUFVFUUHYBUUKUUCLUUHBYKYEXHUUFVGVHRUUCBSYCVIV
      JWDVKVLVMVNVOVPFTVQVRVSYLYCYFHZUUAUUFVTYKYEUULXHYCYFYGWAVBZPYCWBWDWCYLYMW
      EHZUUBYLUULUUNUUMPYCWFWDYMWGWHUUAYNWIWJZYLABYCYMDEYMWKUUMUUOYKYEXHWLYKYEX
      HWMWNXTYTCYMNXMYMLZXSYSAUJUUPXRYREDPNUUPXQYQXKUUPXOYPXPUGUUPXNYOXLJXMYMXI
      UBWOWPWQWRWSWTXAXBXCXDVEXEXFXE $.
      $( [16-Nov-2014] $)

    $( Liouville's approximation theorem extended to complex ` A ` . $)
    aaliou2b $p |- ( A e. AA -> E. k e. NN E. x e. RR+ A. p e. ZZ
        A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ k ) ) <
            ( abs ` ( A - ( p / q ) ) ) ) ) $=
      ( wcel cr cdiv co wceq cfv clt wbr cn cz crp wa c1 cc0 syl cexp cmin cabs
      caa cv wo wral wrex cin elin aaliou2 sylbir wn cim c2 1nn a1i cc wne aacn
      adantr imcl wb reim0b necon3bbid biimpa absrpcl syl2anc rphalfcl cn0 1nn0
      recnd nnexpcl mpan2 ad2antll nnrp rpdivcl rpre znq adantl qre subcl abscl
      cq cle nnge1 1rp rpregt0 ax-mp lediv2 syl3anc mpbid rpcn breqtrd rphalflt
      div1 imsub reim0 oveq2d subid1 3eqtrd fveq2d absimle ltletrd lelttrd olcd
      eqbrtrrd ralrimivva oveq2 breq1d orbi2d 2ralbidv oveq1 rcla42ev pm2.61dan
      ) BUDFZBGFZBEUEZDUEZHIZJZAUEZXSCUEZUAIZHIZBXTUBIZUCKZLMZUFZDNUGEOUGZAPUHC
      NUHZXPXQQBUDGUIFYKBUDGUJABCDEUKULXPXQUMZQZRNFZBUNKZUCKZUOHIZPFZYAYQXSRUAI
      ZHIZYGLMZUFZDNUGEOUGZYKYNYMUPUQYMYPPFZYRYMYOURFZYOSUSZUUDYMYOYMBURFZYOGFX
      PUUGYLBUTZVAZBVBTVLZXPYLUUFXPXQYOSXPUUGXQYOSJVCUUHBVDTVEVFYOVGVHZYPVITZYM
      UUBEDONYMXROFZXSNFZQZQZUUAYAUUPYTYQYGUUPYTPFZYTGFUUPYRYSPFZUUQYMYRUUOUULV
      AZUUPYSNFZUURUUNUUTYMUUMUUNRVJFUUTVKXSRVMVNVOZYSVPTZYQYSVQVHYTVRTUUPYRYQG
      FZUUSYQVRTZUUPYFURFZYGGFUUPUUGXTURFZUVEYMUUGUUOUUIVAZUUPXTUUPXTWDFZXTGFZU
      UOUVHYMXRXSVSVTXTWATZVLZBXTWBVHZYFWCTZUUPYTYQRHIZYQWEUUPRYSWEMZYTUVNWEMZU
      UPUUTUVOUVAYSWFTUUPRGFSRLMQZYSGFSYSLMQZUVCSYQLMQZUVOUVPVCUVQUUPRPFUVQWGRW
      HWIUQUUPUURUVRUVBYSWHTUUPYRUVSUUSYQWHTRYSYQWJWKWLUUPYQURFZUVNYQJUUPYRUVTU
      USYQWMTYQWPTWNUUPYQYPYGUVDUUPUUDYPGFYMUUDUUOUUKVAZYPVRTUVMUUPUUDYQYPLMUWA
      YPWOTUUPYFUNKZUCKZYPYGWEUUPUWBYOUCUUPUWBYOXTUNKZUBIZYOSUBIZYOUUPUUGUVFUWB
      UWEJUVGUVKBXTWQVHUUPUWDSYOUBUUPUVIUWDSJUVJXTWRTWSUUPUUEUWFYOJYMUUEUUOUUJV
      AYOWTTXAXBUUPUVEUWCYGWEMUVLYFXCTXGXDXEXFXHYJUUCYAYBYSHIZYGLMZUFZDNUGEOUGC
      ARYQNPYCRJZYIUWIEDONUWJYHUWHYAUWJYEUWGYGLUWJYDYSYBHYCRXSUAXIWSXJXKXLYBYQJ
      ZUWIUUBEDONUWKUWHUUAYAUWKUWGYTYGLYBYQYSHXMXJXKXLXNWKXO $.
      $( [20-Nov-2014] $)
  $}

  ${
    $d F b c d $.  $d A a b c d $.  $d B a b c d $.  $d G a b d $.
    aaliou3lem.a $e |- G = ( c e. ( ZZ>= ` A ) |->
        ( ( 2 ^ -u ( ! ` A ) ) x. ( ( 1 / 2 ) ^ ( c - A ) ) ) ) $.
    $( Lemma for ~ aaliou3 . $)
    aaliou3lem1 $p |- ( ( A e. NN /\ B e. ( ZZ>= ` A ) ) ->
        ( G ` B ) e. RR ) $=
      ( cn wcel cfv c2 cexp co cmin cmul cr wceq oveq2d crp cz 2re elrpii wa c1
      cuz cfa cneg cdiv oveq1 ovex fvmpt adantl 2pos cn0 simpl nnnn0 faccl 3syl
      cv nnz znegcl rpexpcl sylancr 2ne0 halfgt0 eluzelz zsubcl syl2anr rpmulcl
      rereccli syl2anc rpre syl eqeltrd ) AFGZBAUCHZGZUAZBCHZIAUDHZUEZJKZUBIUFK
      ZBALKZJKZMKZNVOVQWDOVMDBVTWADUQZALKZJKZMKWDVNCWEBOZWGWCVTMWHWFWBWAJWEBALU
      GPPEVTWCMUHUIUJVPWDQGZWDNGVPVTQGZWCQGZWIVPIQGVSRGZWJISUKTVPVRFGZVRRGWLVPV
      MAULGWMVMVOUMAUNAUOUPVRURVRUSUPIVSUTVAVPWAQGWBRGZWKWAISVBVHVCTVOBRGARGWNV
      MABVDAURBAVEVFWAWBUTVAVTWCVGVIWDVJVKVL $.
      $( [16-Nov-2014] $)

    aaliou3lem.b $e |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) ) $.
    $( Lemma for ~ aaliou3 . $)
    aaliou3lem2 $p |- ( ( A e. NN /\ B e. ( ZZ>= ` A ) ) ->
        ( F ` B ) e. ( 0 (,] ( G ` B ) ) ) $=
      ( wcel cfv co wbr cle c2 cexp wceq oveq2d syl c1 cmul vb vd cn cuz wa cc0
      cioc cr clt cxr w3a wb 0xr aaliou3lem1 elioc2 sylancr crp cfa cneg sselda
      uznnssnn cv fveq2 negeqd ovex fvmpt cz 2re 2pos elrpii cn0 nnnn0 3syl nnz
      faccl znegcl rpexpcl eqeltrd rpre rpgt0 wi caddc breq12d imbi2d cdiv cmin
      weq leid cc nncn subid 2ne0 rereccli recni exp0 ax-mp syl6eq mulid1 eqtrd
      rpcn breqtrrd uzid oveq1 3brtr4d a1i rpge0 halfgt0 eluzelz zsubcl syl2anr
      simpl rpmulcl syl2anc jca31 adantr adantl simpr zcn mulneg1 nnmulcl nnge1
      zmulcl 1re nnre leneg mpbid eqbrtrd 1nn0 nn0negzi eluz mpbird 1lt2 ltleii
      sylancl expwordi mp3an12 2cn expn1 ax-1cn syl3anc syl6breq lemul12a facp1
      3impia syl112anc addcom peano2cn adddi oveq1d 3eqtr3d wne rpcnne0 expaddz
      mpan addsub eluzle znn0sub2 expp1 mulass eqtr4d sylibrd peano2nn peano2uz
      ex 3imtr4d expcom a2d uzind4 impcom mpbir3and ) AUCIZBAUDJZIZUEZBCJZUFBDJ
      ZUGKIZUVOUHIZUFUVOUILZUVOUVPMLZUVNUFUJIUVPUHIUVQUVRUVSUVTUKULUMABDFGUNUFU
      VPUVOUOUPUVNUVOUQIZUVRUVNUVONBURJZUSZOKZUQUVNBUCIZUVOUWDPUVKUVLUCBAVAZUTZ
      EBNEVBZURJZUSZOKZUWDUCCUWHBPZUWJUWCNOUWLUWIUWBUWHBURVCVDQHNUWCOVEVFRUVNNU
      QIZUWCVGIZUWDUQINVHVIVJZUVNUWBUCIZUWBVGIUWNUVNUWEBVKIUWPUWGBVLBVOVMUWBVNU
      WBVPVMNUWCVQUPVRZUVOVSRUVNUWAUVSUWQUVOVTRUVMUVKUVTUVKUAVBZCJZUWRDJZMLZWAU
      VKACJZADJZMLZWAZUVKUBVBZCJZUXFDJZMLZWAUVKUXFSWBKZCJZUXJDJZMLZWAUVKUVTWAUA
      UBABUWRAPZUXAUXDUVKUXNUWSUXBUWTUXCMUWRACVCUWRADVCWCWDUAUBWGZUXAUXIUVKUXOU
      WSUXGUWTUXHMUWRUXFCVCUWRUXFDVCWCWDUWRUXJPZUXAUXMUVKUXPUWSUXKUWTUXLMUWRUXJ
      CVCUWRUXJDVCWCWDUWRBPZUXAUVTUVKUXQUWSUVOUWTUVPMUWRBCVCUWRBDVCWCWDUXEAVGIZ
      UVKNAURJZUSZOKZUYASNWEKZAAWFKZOKZTKZUXBUXCMUVKUYAUYAUYEMUVKUYAUQIZUYAUHIU
      YAUYAMLUVKUWMUXTVGIZUYFUWOUVKUXSUCIZUXSVGIZUYGUVKAVKIZUYHAVLZAVOZRUXSVNZU
      XSVPZVMNUXTVQZUPZUYAVSUYAWHVMUVKUYEUYASTKZUYAUVKUYDSUYATUVKUYDUYBUFOKZSUV
      KUYCUFUYBOUVKAWIIZUYCUFPAWJZAWKRQUYBWIIZUYRSPUYBNVHWLWMZWNZUYBWOWPWQQUVKU
      YFUYAWIIZUYQUYAPUYPUYAWTZUYAWRVMWSXAEAUWKUYAUCCUWHAPZUWJUXTNOVUFUWIUXSUWH
      AURVCVDQHNUXTOVEVFUVKUXRAUVLIUXCUYEPAVNZAXBFAUYAUYBFVBZAWFKZOKZTKZUYEUVLD
      VUHAPZVUJUYDUYATVULVUIUYCUYBOVUHAAWFXCQQGUYAUYDTVEVFVMXDXEUXFUVLIZUVKUXIU
      XMUVKVUMUXIUXMWAUVKVUMUEZNUXFURJZUSZOKZUYAUYBUXFAWFKZOKZTKZMLZNUXJURJZUSZ
      OKZUYAUYBUXJAWFKZOKZTKZMLZUXIUXMVUNVVAVUQNVUPUXFTKZOKZTKZVUTUYBTKZMLZVVHV
      UNVVAVVMVUNVVAUEVUQUHIZUFVUQMLZUEVUTUHIZUEZVVJUHIZUFVVJMLZUEUYBUHIZUEZVVA
      VVJUYBMLZVVMVUNVVQVVAVUNVVNVVOVVPVUNVUQUQIZVVNVUNUWMVUPVGIZVWCUWOVUNVUOUC
      IZVUOVGIVWDVUNUXFUCIZUXFVKIZVWEUVKUVLUCUXFUWFUTZUXFVLZUXFVOVMZVUOVNVUOVPV
      MZNVUPVQUPZVUQVSRVUNVWCVVOVWLVUQXFRVUNVUTUQIZVVPVUNUYFVUSUQIZVWMVUNUWMUYG
      UYFUWOVUNUYHUYIUYGVUNUVKUYJUYHUVKVUMXKUYKUYLVMUYMUYNVMUYOUPZVUNUYBUQIVURV
      GIZVWNUYBVUBXGVJVUMUXFVGIZUXRVWPUVKAUXFXHZVUGUXFAXIXJUYBVURVQUPZUYAVUSXLX
      MVUTVSRXNXOVUNVWAVVAVUNVVRVVSVVTVUNVVJUQIZVVRVUNUWMVVIVGIZVWTUWOVUNVWDVWQ
      VXAVWKVUMVWQUVKVWRXPZVUPUXFYBXMZNVVIVQUPZVVJVSRVUNVWTVVSVXDVVJXFRVVTVUNVU
      BXEXNXOVUNVVAXQVUNVWBVVAVUNVVJNSUSZOKZUYBMVUNVXEVVIUDJIZVVJVXFMLZVUNVXGVV
      IVXEMLZVUNVVIVUOUXFTKZUSZVXEMVUNVUOWIIZUXFWIIZVVIVXKPVUNVWEVXLVWJVUOWJRZV
      UNVWQVXMVXBUXFXRZRZVUOUXFXSXMVUNSVXJMLZVXKVXEMLZVUNVXJUCIZVXQVUNVWEVWFVXS
      VWJVWHVUOUXFXTXMZVXJYARVUNSUHIVXJUHIZVXQVXRULYCVUNVXSVYAVXTVXJYDRSVXJYEUP
      YFYGVUNVXAVXEVGIVXGVXIULVXCSYHYIVVIVXEYJYNYKNUHISNMLVXGVXHVHSNYCVHYLYMNVV
      IVXEYOYPRNWIIZVXFUYBPYQNYRWPUUAXOVVQVWAVVAVWBUEVVMVUQVUTVVJUYBUUBUUDUUEUV
      DVUNVVDVVKVVGVVLMVUNVVDNVUPVVIWBKZOKZVVKVUNVVCVYCNOVUNVVCVUOUXJTKZUSZVYCV
      UNVVBVYEVUNVWFVWGVVBVYEPVWHVWIUXFUUCVMVDVUNVUPUXJTKZVUPSUXFWBKZTKZVYFVYCV
      UNUXJVYHVUPTVUNVXMSWIIZUXJVYHPVXPYSUXFSUUFYNQVUNVXLUXJWIIZVYGVYFPVXNVUNVW
      QVXMVYKVXBVXOUXFUUGVMVUOUXJXSXMVUNVYIVUPSTKZVVIWBKZVYCVUNVUPWIIZVYJVXMVYI
      VYMPVUNVWDVYNVWKVUPXRZRVYJVUNYSXEZVXPVUPSUXFUUHYTVUNVYLVUPVVIWBVUNVWDVYNV
      YLVUPPVWKVYOVUPWRVMUUIWSUUJWSQVUNVWDVXAVYDVVKPZVWKVXCVYBNUFUUKUEZVWDVXAUE
      VYQUWMVYRUWONUULWPNVUPVVIUUMUUNXMWSVUNVVGUYAVUSUYBTKZTKZVVLVUNVVFVYSUYATV
      UNVVFUYBVURSWBKZOKZVYSVUNVVEWUAUYBOVUNVXMVYJUYSVVEWUAPVXPVYPUVKUYSVUMUYTX
      OUXFSAUUOYTQVUNVUAVURVKIZWUBVYSPVUCVUNUXRVWQAUXFMLZWUCUVKUXRVUMVUGXOVXBVU
      MWUDUVKAUXFUUPXPAUXFUUQYTUYBVURUURUPWSQVUNVUDVUSWIIZVUAVVLVYTPVUNUYFVUDVW
      OVUERVUNVWNWUEVWSVUSWTRVUAVUNVUCXEUYAVUSUYBUUSYTUUTWCUVAVUNUXGVUQUXHVUTMV
      UNVWFUXGVUQPVWHEUXFUWKVUQUCCEUBWGZUWJVUPNOWUFUWIVUOUWHUXFURVCVDQHNVUPOVEV
      FRVUMUXHVUTPUVKFUXFVUKVUTUVLDFUBWGZVUJVUSUYATWUGVUIVURUYBOVUHUXFAWFXCQQGU
      YAVUSTVEVFXPWCVUNUXKVVDUXLVVGMVUNVWFUXJUCIUXKVVDPVWHUXFUVBEUXJUWKVVDUCCUW
      HUXJPZUWJVVCNOWUHUWIVVBUWHUXJURVCVDQHNVVCOVEVFVMVUMUXLVVGPZUVKVUMUXJUVLIW
      UIAUXFUVCFUXJVUKVVGUVLDVUHUXJPZVUJVVFUYATWUJVUIVVEUYBOVUHUXJAWFXCQQGUYAVV
      FTVEVFRXPWCUVEUVFUVGUVHUVIUVJ $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aaliou3 . $)
    aaliou3lem3 $p |- ( A e. NN -> ( seq A ( + , F ) e. dom ~~> /\
        sum_ b e. ( ZZ>= ` A ) ( F ` b ) e. RR+ /\
        sum_ b e. ( ZZ>= ` A ) ( F ` b ) <_
          ( 2 x. ( 2 ^ -u ( ! ` A ) ) ) ) ) $=
      ( wcel cfv crp c2 co cle wbr syl cc0 c1 cdiv cc cn caddc cseq cli cdm cuz
      cv csu cfa cneg cexp cmul eqid cz nnz uzid aaliou3lem1 wa cr clt cioc w3a
      aaliou3lem2 cxr 0xr elioc2 sylancr mpbid simp1d cmin 2cn 2ne0 reccli cabs
      wb a1i wceq 2re rereccli halfgt0 elrpii rprege0 mp2b halflt1 eqbrtri 2pos
      absid cn0 nnnn0 faccl znegcl 3syl rpexpcl rpcn geolim3 breldm simp2d elrp
      seqex sylanbrc rpge0 simp3d cvgcmp eqidd isumrpcl eqid1 isumle recnd ovex
      cvv isumclim ax-1cn 2halves ax-mp subaddrii oveq2i mulcl sylancl div1 wne
      1rp rpcnne0 divdiv2 mp3an23 mulcom 3eqtr4d syl5eq eqtrd breqtrd 3jca ) AU
      AIZUBBAUCUDUEZIAUFJZEUGZBJZEUHZKIYPLLAUIJZUJZUKMZULMZNOYKECBAAYMYMUMZYKAU
      NIAYMIAUOZAUPPZAYNCFGUQZYKYNYMIURZYOUSIZQYOUTOZYOYNCJZNOZUUEYOQUUHVAMIZUU
      FUUGUUIVBZAYNBCDFGHVCUUEQVDIUUHUSIUUJUUKVOVEUUDQUUHYOVFVGVHZVIZYKUBCAUCZY
      SRRLSMZVJMZSMZUDOUUNYLIYKAUUOYSFCUUBUUOTIYKLVKVLVMZVPUUOVNJZRUTOYKUUSUUOR
      UTUUOKIUUOUSIQUUONOURUUSUUOVQUUOLVRVLVSVTWAUUOWBUUOWGWCWDWEVPYKYSKIZYSTIZ
      YKLKIZYRUNIZUUTLVRWFWAZYKYQUAIZYQUNIUVCYKAWHIUVEAWIAWJPYQUOYQWKWLLYRWMVGY
      SWNPZGWOZUUNUUQUDUBCAWSWPPZUUEYOKIZQYONOUUEUUFUUGUVIUUMUUEUUFUUGUUIUULWQY
      OWRWTZYOXAPUUEUUFUUGUUIUULXBZXCZYKYOEBAAYMYMUUAUUAUUCUUEYOXDZUVJUVLXEYKYP
      YMUUHEUHZYTNYKYOUUHEBCAYMYMXFUUBUVMUUMUUEUUHXDZUUDUVKUVLUVHXGYKUVNUUQYTYK
      UUHUUQECAXJYMUUAUUBUVOUUEUUHUUDXHUUQXJIYKYSUUPSXIVPUVGXKYKUUQYSUUOSMZYTUU
      PUUOYSSRUUOUUOXLUURUURRTIZUUOUUOUBMRVQXLRXMXNXOXPYKYSLULMZRSMZUVRUVPYTYKU
      VRTIZUVSUVRVQYKUVALTIZUVTUVFVKYSLXQXRUVRXSPYKUVAUVPUVSVQZUVFUVAUVQRQXTURZ
      UWALQXTURZUWBRKIUWCYARYBXNUVBUWDUVDLYBXNYSRLYCYDPYKUWAUVAYTUVRVQVKUVFLYSY
      EVGYFYGYHYIYJ $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d A a b x $.  $d B a b x $.

    $( Lemma for ~ aaliou3 .  Exponential sequences are cofinal in the
       reals. $)
    aaliou3lem8 $p |- ( ( ( A e. RR /\ 1 < A ) /\ B e. RR ) -> E. x e. NN B <
        ( A ^ x ) ) $=
      ( cr wcel c1 clt wbr wa co cexp cz cle cfv cc0 crp a1i 1re syl syl2anc va
      cv caddc wrex cn cif clog cdiv cfl wne 1rp wn simplr lt01 wo simpr letric
      sylancl orcanai ltletrd elrp sylanbrc ifclda relogcl simpll lttrd syl3anc
      0re ltne logne0 redivcl flcl ifcl sylancr peano2zdi rpre max1 cmul flltp1
      rpexpcl zre rplogcl adantr sylib ltdivmul2 mpbid relogexp breqtrrd logltb
      wb mpbird lelttrd oveq1 oveq2d breq2d rcla4ev simprl 1z elnnz1 simprr cuz
      wceq simplll wi ltle mpd max2 eluz expwordi oveq2 exp32 rexlimdv ) BDEZFB
      GHZIZCDEZIZCBUAUBZFUCJZKJZGHZUALUDZCBAUBZKJZGHZAUEUDZXQCFMHZFCUFZUGNZBUGN
      ZUHJZUINZLEZCBYLFUCJZKJZGHZYBXQYKDEZYMXQYIDEZYJDEZYJOUJZYQXQYHPEZYRXQYGFC
      PFPEXQYGIUKQXQYGULZIZXPOCGHCPEXOXPUUBUMZUUCOFCODEZUUCVHQFDEZUUCRQUUDOFGHZ
      UUCUNQXQYGFCMHZXQXPUUFYGUUHUOXOXPUPZRCFUQURUSUTCVAVBVCZYHVDSZXQBPEZYSXQXM
      OBGHUULXMXNXPVEZXQOFBUUEXQVHQUUFXQRQZUUMUUGXQUNQXMXNXPUMZVFBVAVBZBVDSXQUU
      LBFUJZYTUUPXQUUFXMXNUUQUUNUUMUUOFBVIVGBVJTYIYJVKVGZYKVLSZXQCYHYOUUIXQUUFX
      PYHDERUUIYGFCDVMVNXQYOPEZYODEXQUULYNLEZUUTUUPXQYLUUSVOZBYNVTTZYOVPSXQXPUU
      FCYHMHUUIRCFVQURXQYHYOGHZYIYOUGNZGHZXQYIYNYJVRJZUVEGXQYKYNGHZYIUVGGHZXQYQ
      UVHUURYKVSSXQYRYNDEZYSOYJGHIZUVHUVIWJUUKXQUVAUVJUVBYNWASXQYJPEZUVKXOUVLXP
      BWBWCYJVAWDYIYNYJWEVGWFXQUULUVAUVEUVGXBUUPUVBBYNWGTWHXQUUAUUTUVDUVFWJUUJU
      VCYHYOWITWKWLYAYPUAYLLXRYLXBZXTYOCGUVMXSYNBKXRYLFUCWMWNWOWPTXQYAYFUALXQXR
      LEZYAYFXQUVNYAIZIZFXSMHZXSFUFZUEEZCBUVRKJZGHZYFUVPUVRLEZFUVRMHZUVSUVPXSLE
      ZFLEUWBUVPXRXQUVNYAWQVOZWRUVQXSFLVMURZUVPUUFXSDEZUWCRUVPUWDUWGUWEXSWASZFX
      SVQVNUVRWSVBUVPCXTUVTXOXPUVOUMUVPXTPEZXTDEUVPUULUWDUWIXQUULUVOUUPWCZUWEBX
      SVTTXTVPSUVPUVTPEZUVTDEUVPUULUWBUWKUWJUWFBUVRVTTUVTVPSXQUVNYAWTUVPXMFBMHZ
      UVRXSXANEZXTUVTMHXMXNXPUVOXCXQUWLUVOXQXNUWLUUOXQUUFXMXNUWLXDRUUMFBXEVNXFW
      CUVPUWMXSUVRMHZUVPUUFUWGUWNRUWHFXSXGVNUVPUWDUWBUWMUWNWJUWEUWFXSUVRXHTWKBX
      SUVRXIVGUTYEUWAAUVRUEYCUVRXBYDUVTCGYCUVRBKXJWOWPTXKXLXF $.
      $( [20-Nov-2014] $)

    $( Lemma for ~ aaliou3 . $)
    aaliou3lem9 $p |- ( ( A e. NN /\ B e. RR+ ) -> E. x e. NN ( 2 x. ( 2 ^ -u (
        ! ` ( x + 1 ) ) ) ) <_ ( B / ( ( 2 ^ ( ! ` x ) ) ^ A ) ) ) $=
      ( cn wcel crp c2 cdiv co cexp wbr c1 cmul cle cr syl2anc syl wceq syl3anc
      cc va wa cv clt wrex caddc cfa cfv cneg 2re 1lt2 pm3.2i rerpdivcl sylancr
      simpr aaliou3lem8 cmin simprl simpll nnaddm1cl simplr cn0 reexpcl cz 2pos
      nnnn0 elrpii nnaddcl nnm1nn0 peano2nn0 faccl zmulcl zsubcl rpexpcl simprr
      nnz rpre wi ltle mpd cuz a1i 1re ltleii cc0 nnre nnge1 lemulge12 syl22anc
      nn0ge0 facp1 oveq1d nn0cn subdi ax-1cn npcan pncan eqtrd 3eqtr2d breqtrrd
      nncn oveq2d wb eluz mpbird expwordi letrd wne rpcnne0 expsub syl12anc 2cn
      ax-mp expmul rpcn rpne0 3eqtrrd rpreccl rpmulcl elrp sylib ledivmul mpbid
      divrec mul12 breqtrd expneg eqtr4d 3brtr4d fveq2d negeqd breq12d rexlimdv
      oveq1 fveq2 rcla4ev exp32 ) BDEZCFEZUBZGCHIZGUAUCZJIZUDKZUADUEZGGAUCZLUFI
      ZUGUHZUIZJIZMIZCGUUFUGUHZJIZBJIZHIZNKZADUEZYTGOEZLGUDKZUBUUAOEZUUEUURUUSU
      JUKULYTUURYSUUTUJYRYSUOGCUMZUNUAGUUAUPUNYTUUDUUQUADYTUUBDEZUUDUUQYTUVBUUD
      UBZUBZUUBBUFIZLUQIZDEZGGUVFLUFIZUGUHZUIZJIZMIZCGUVFUGUHZJIZBJIZHIZNKZUUQU
      VDUVBYRUVGYTUVBUUDURZYRYSUVCUSZUUBBUTPUVDGGUVIJIZHIZCLUVOHIZMIZUVLUVPNUVD
      UWAUWCNKZGUVTUWCMIZNKZUVDGCUVTUWBMIZMIZUWENUVDUUAUWGNKZGUWHNKZUVDUUAGUVIU
      VMBMIZUQIZJIZUWGNUVDUUAUUCUWMUVDUURYSUUTUJYRYSUVCVAZUVAUNZUVDUURUUBVBEZUU
      COEZUJUVDUVBUWPUVRUUBVFQZGUUBVCUNZUVDUWMFEZUWMOEUVDGFEZUWLVDEZUWTGUJVEVGZ
      UVDUVIVDEZUWKVDEZUXBUVDUVIDEZUXDUVDUVHVBEZUXFUVDUVFVBEZUXGUVDUVEDEZUXHUVD
      UVBYRUXIUVRUVSUUBBVHPZUVEVIQZUVFVJQZUVHVKQZUVIVPQZUVDUVMVDEZBVDEZUXEUVDUV
      MDEZUXOUVDUXHUXQUXKUVFVKQZUVMVPQZUVDYRUXPUVSBVPQZUVMBVLPZUVIUWKVMPZGUWLVN
      UNUWMVQQUVDUUDUUAUUCNKZYTUVBUUDVOUVDUUTUWQUUDUYCVRUWOUWSUUAUUCVSPVTUVDUUR
      LGNKZUWLUUBWAUHEZUUCUWMNKUURUVDUJWBZUYDUVDLGWCUJUKWDWBUVDUYEUUBUWLNKZUVDU
      UBUVMUUBMIZUWLNUVDUUBOEZUVMOEZWEUUBNKZLUVMNKZUUBUYHNKUVDUVBUYIUVRUUBWFQUV
      DUXQUYJUXRUVMWFQUVDUWPUYKUWRUUBWJQUVDUXQUYLUXRUVMWGQUUBUVMWHWIUVDUWLUVMUV
      HMIZUWKUQIZUVMUVHBUQIZMIZUYHUVDUVIUYMUWKUQUVDUXHUVIUYMRUXKUVFWKQWLUVDUVMT
      EZUVHTEZBTEZUYPUYNRUVDUXQUYQUXRUVMXAQUVDUXGUYRUXLUVHWMQUVDYRUYSUVSBXAQZUV
      MUVHBWNSUVDUYOUUBUVMMUVDUYOUVEBUQIZUUBUVDUVHUVEBUQUVDUVETEZLTEZUVHUVERUVD
      UXIVUBUXJUVEXAQVUCUVDWOWBUVELWPPWLUVDUUBTEZUYSVUAUUBRUVDUVBVUDUVRUUBXAQUY
      TUUBBWQPWRXBWSWTUVDUUBVDEZUXBUYEUYGXCUVDUVBVUEUVRUUBVPQUYBUUBUWLXDPXEGUUB
      UWLXFSXGUVDUWMUVTGUWKJIZHIZUVTUVOHIZUWGUVDGTEZGWEXHUBZUXDUXEUWMVUGRVUJUVD
      UXAVUJUXCGXIXMWBUXNUYAGUVIUWKXJXKUVDVUFUVOUVTHUVDVUIUVMVBEZBVBEZVUFUVORVU
      IUVDXLWBZUVDUXQVUKUXRUVMVFQUVDYRVULUVSBVFQGUVMBXNSXBUVDUVTTEZUVOTEZUVOWEX
      HZVUHUWGRUVDUVTFEZVUNUVDUXAUXDVUQUXCUXNGUVIVNUNZUVTXOQZUVDUVOFEZVUOUVDUVN
      FEZUXPVUTUVDUXAUXOVVAUXCUXSGUVMVNUNUXTUVNBVNPZUVOXOQZUVDVUTVUPVVBUVOXPQZU
      VTUVOYDSXQWTUVDUURUWGOEZCOEWECUDKUBZUWIUWJXCUYFUVDUWGFEZVVEUVDVUQUWBFEZVV
      GVURUVDVUTVVHVVBUVOXRQZUVTUWBXSPUWGVQQUVDYSVVFUWNCXTYAGUWGCYBSYCUVDCTEZVU
      NUWBTEZUWHUWERUVDYSVVJUWNCXOQZVUSUVDVVHVVKVVIUWBXOQCUVTUWBYESYFUVDUURUWCO
      EZUVTOEWEUVTUDKUBZUWDUWFXCUYFUVDUWCFEZVVMUVDYSVVHVVOUWNVVICUWBXSPUWCVQQUV
      DVUQVVNVURUVTXTYAGUWCUVTYBSXEUVDUVLGLUVTHIZMIZUWAUVDUVKVVPGMUVDVUIUVIVBEZ
      UVKVVPRXLUVDUXFVVRUXMUVIVFQGUVIYGUNXBUVDVUIVUNUVTWEXHZUWAVVQRVUMVUSUVDVUQ
      VVSVURUVTXPQGUVTYDSYHUVDVVJVUOVUPUVPUWCRVVLVVCVVDCUVOYDSYIUUPUVQAUVFDUUFU
      VFRZUUKUVLUUOUVPNVVTUUJUVKGMVVTUUIUVJGJVVTUUHUVIVVTUUGUVHUGUUFUVFLUFYNYJY
      KXBXBVVTUUNUVOCHVVTUUMUVNBJVVTUULUVMGJUUFUVFUGYOXBWLXBYLYPPYQYMVT $.
      $( [20-Nov-2014] $)
  $}

  ${
    $d a b c d e $.  $d F b c d e $.  $d L c d e f $.  $d H b d e f $.
    $d A a b c d e $.  $d B a b c d e $.
    aaliou3lem.c $e |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) ) $.
    aaliou3lem.d $e |- L = sum_ b e. NN ( F ` b ) $.
    aaliou3lem.e $e |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) ) $.
    $( Lemma for ~ aaliou3 . $)
    aaliou3lem4 $p |- L e. RR $=
      ( c1 cfv cv csu cr cn wcel c2 cexp co cmul cuz nnuz sumeq1i eqtri crp 1nn
      cseq cli cdm cfa cneg cle wbr cdiv cmin cmpt eqid aaliou3lem3 simp2d rpre
      caddc mp2b eqeltri ) CJUAKZELAKZEMZNCOVEEMVFHOVDVEEUBUCUDJOPZVFUEPZVFNPUF
      VGVAAJUGUHUIPVHVFQQJUJKUKRSZTSULUMJAFVDVIJQUNSFLJUOSRSTSUPZDEFVJUQGURUSVF
      UTVBVC $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aaliou3 . $)
    aaliou3lem5 $p |- ( A e. NN -> ( H ` A ) e. RR ) $=
      ( cn wcel cfv c1 cfz co cv cr c2 cexp csu oveq2 sumeq1d sumex fvmpt fzfid
      wceq wa elfznn adantl cfa cneg weq fveq2 negeqd oveq2d ovex crp cz elrpii
      2re 2pos cn0 nnnn0 faccl syl nnz znegcl 3syl rpexpcl sylancr rpre eqeltrd
      fsumrecl ) AKLZACMNAOPZFQZBMZFUAZRGANGQZOPZVRFUAVSKCVTAUGWAVPVRFVTANOUBUC
      JVPVRFUDUEVOVPVRFVONAUFVOVQVPLZUHVQKLZVRRLWBWCVOVQAUIUJWCVRSVQUKMZULZTPZR
      EVQSEQZUKMZULZTPWFKBEFUMZWIWESTWJWHWDWGVQUKUNUOUPHSWETUQUEWCWFURLZWFRLWCS
      URLWEUSLZWKSVAVBUTWCWDKLZWDUSLWLWCVQVCLWMVQVDVQVEVFWDVGWDVHVISWEVJVKWFVLV
      FVMVFVNVM $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aaliou3 . $)
    aaliou3lem6 $p |- ( A e. NN -> ( ( H ` A ) x.
          ( 2 ^ ( ! ` A ) ) ) e. ZZ ) $=
      ( cn wcel c2 cexp co cmul cz cc cn0 syl cfv cfa c1 cfz wceq oveq2 sumeq1d
      csu sumex fvmpt oveq1d fzfid crp 2re 2pos elrpii nnnn0 faccl 3syl rpexpcl
      cv nnz sylancr rpcn wa cneg elfznn fveq2 negeqd oveq2d ovex adantl znegcl
      weq eqeltrd fsummulc1 caddc adantr cc0 rpcnne0 ax-mp expaddz mpan syl2anc
      wne 2z cmin zcn addcom nncn negsub eqtrd cle wbr elfzle2 facwordi syl3anc
      wb nn0sub mpbid zexpcl eqeltrrd fsumzcl ) AKLZACUAZMAUBUAZNOZPOUCAUDOZFVA
      ZBUAZFUHZXGPOZQXDXEXKXGPGAUCGVAZUDOZXJFUHXKKCXMAUEXNXHXJFXMAUCUDUFUGJXHXJ
      FUIUJUKXDXLXHXJXGPOZFUHQXDXHXJXGFXDUCAULZXDXGUMLZXGRLXDMUMLZXFQLZXQMUNUOU
      PZXDASLZXFKLZXSAUQZAURZXFVBUSZMXFUTVCXGVDTXDXIXHLZVEZXJMXIUBUAZVFZNOZRYFX
      JYJUEZXDYFXIKLZYKXIAVGZEXIMEVAZUBUAZVFZNOYJKBEFVNZYPYIMNYQYOYHYNXIUBVHVIV
      JHMYINVKUJTVLZYGYJUMLZYJRLYGXRYIQLZYSXTYGYHKLZYHQLYTYGYLXISLZUUAYFYLXDYMV
      LZXIUQZXIURZUSZYHVBYHVMUSZMYIUTVCYJVDTVOVPXDXHXOFXPYGXOYJXGPOZQYGXJYJXGPY
      RUKYGMYIXFVQOZNOZUUHQYGYTXSUUJUUHUEZUUGXDXSYFYEVRZMRLMVSWEVEZYTXSVEUUKXRU
      UMXTMVTWAMYIXFWBWCWDYGMQLUUISLUUJQLWFYGUUIXFYHWGOZSYGUUIXFYIVQOZUUNYGYIRL
      ZXFRLZUUIUUOUEYGYTUUPUUGYIWHTYGXSUUQUULXFWHTZYIXFWIWDYGUUQYHRLZUUOUUNUEUU
      RYGUUAUUSUUFYHWJTXFYHWKWDWLYGYHXFWMWNZUUNSLZYGUUBYAXIAWMWNZUUTYGYLUUBUUCU
      UDTZXDYAYFYCVRZYFUVBXDXIUCAWOVLXIAWPWQYGYHSLZXFSLZUUTUVAWRYGUUBUUAUVEUVCU
      UEYHUQUSYGYAYBUVFUVDYDXFUQUSYHXFWSWDWTVOMUUIXAVCXBVOXCVOVO $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aaliou3 . $)
    aaliou3lem7 $p |- ( A e. NN -> ( ( H ` A ) =/= L /\
        ( abs ` ( L - ( H ` A ) ) ) <_
          ( 2 x. ( 2 ^ -u ( ! ` ( A + 1 ) ) ) ) ) ) $=
      ( cn wcel c1 caddc co cfv crp c2 cexp wbr cuz cv csu cfa cneg cmul cle wa
      wne cmin cabs cseq cli cdm w3a peano2nn cdiv cmpt eqid aaliou3lem3 3simpc
      3syl wceq wb cfz cc nncn ax-1cn pncan sylancl oveq2d sumeq1d oveq1d eqid1
      nnuz eqidd weq fveq2 negeqd ovex fvmpt cz 2re 2pos elrpii cn0 nnnn0 faccl
      syl nnz znegcl rpexpcl sylancr rpcn eqeltrd adantl simp1d ax-mp isumsplit
      1nn a1i oveq2 sumex 3eqtr4rd syl6eqr aaliou3lem4 recni aaliou3lem5 simp2d
      recnd subadd syl3anc mpbird eqcomd eleq1 breq1 cr clt adantr simprl difrp
      anbi12d ltne necomd rpmulcl rpre absdifle resubcl syl2anc ltsubrp wi ltle
      lttrd mpd simprr lesubadd2 mpbid mpbir2and jca ex sylbid ) AKLZAMNOZUAPZF
      UBZBPZFUCZQLZUUGRRUUCUDPZUEZSOZUFOZUGTZUHZACPZDUIZDUUOUJOZUKPUULUGTZUHZUU
      BUUCKLZNBUUCULUMUNZLZUUHUUMUOUUNAUPZUUCBGUUDUUKMRUQOZGUBZUUCUJOSOUFOURZEF
      GUVFUSHUTZUVBUUHUUMVAVBUUBUUNUUQQLZUUQUULUGTZUHZUUSUUBUUGUUQVCZUUNUVJVDUU
      BUUQUUGUUBUUQUUGVCZUUOUUGNOZDVCZUUBUVMKUUFFUCZDUUBMUUCMUJOZVEOZUUFFUCZUUG
      NOMAVEOZUUFFUCZUUGNOUVOUVMUUBUVRUVTUUGNUUBUVQUVSUUFFUUBUVPAMVEUUBAVFLMVFL
      UVPAVCAVGVHAMVIVJVKVLVMUUBUUFFBMUUCUUDKVOUUDVNUVCUUBUUEKLZUHUUFVPUWAUUFVF
      LUUBUWAUUFRUUEUDPZUEZSOZVFEUUEREUBZUDPZUEZSOUWDKBEFVQZUWGUWCRSUWHUWFUWBUW
      EUUEUDVRVSVKHRUWCSVTWAUWAUWDQLZUWDVFLUWARQLZUWCWBLZUWIRWCWDWEZUWAUWBKLZUW
      BWBLUWKUWAUUEWFLUWMUUEWGUUEWHWIUWBWJUWBWKVBRUWCWLWMUWDWNWIWOWPNBMULUVALZU
      UBMKLZUWNWTUWOUWNMUAPZUUFFUCZQLUWQRRMUDPUESOZUFOUGTMBGUWPUWRUVDUVEMUJOSOU
      FOURZEFGUWSUSHUTWQWRXAWSUUBUUOUVTUUGNGAMUVEVEOZUUFFUCUVTKCUVEAVCUWTUVSUUF
      FUVEAMVEXBVLJUVSUUFFXCWAVMXDIXEUUBDVFLZUUOVFLUUGVFLZUVLUVNVDUXAUUBDBCDEFG
      HIJXFZXGXAUUBUUOABCDEFGHIJXHZXJUUBUUTUUHUXBUVCUUTUVBUUHUUMUVGXIUUGWNVBDUU
      OUUGXKXLXMXNUVKUUHUVHUUMUVIUUGUUQQXOUUGUUQUULUGXPYBWIUUBUVJUUSUUBUVJUHZUU
      PUURUXEDUUOUXEUUOXQLZDXQLZUUODXRTZDUUOUIUUBUXFUVJUXDXSZUXGUXEUXCXAZUXEUXH
      UVHUUBUVHUVIXTUXEUXFUXGUXHUVHVDUXIUXCUUODYAVJXMZUUODYCXLYDUXEUURUUOUULUJO
      ZDUGTZDUUOUULNOUGTZUXEUXGUXFUULXQLZUURUXMUXNUHVDUXJUXIUXEUULQLZUXOUUBUXPU
      VJUUBUWJUUKQLZUXPUWLUUBUWJUUJWBLZUXQUWLUUBUUIKLZUUIWBLUXRUUBUUTUUCWFLUXSU
      VCUUCWGUUCWHVBUUIWJUUIWKVBRUUJWLWMRUUKYEWMXSZUULYFWIZDUUOUULYGXLUXEUXLDXR
      TZUXMUXEUXLUUODUXEUXFUXOUXLXQLZUXIUYAUUOUULYHYIZUXIUXJUXEUXFUXPUXLUUOXRTU
      XIUXTUUOUULYJYIUXKYMUXEUYCUXGUYBUXMYKUYDUXCUXLDYLVJYNUXEUVIUXNUUBUVHUVIYO
      UXEUXGUXFUXOUVIUXNVDUXJUXIUYADUUOUULYPXLYQYRYSYTUUAYN $.
      $( [16-Nov-2014] $)

    $d L a b c d e f $.

    $( Example of a "Liouville number", a very simple definable transcedental
       real. $)
    aaliou3 $p |- -. L e. AA $=
      ( vf vd wcel cdiv co cn cz crp wn c2 cr ve caa cv wceq cexp cmin cabs cfv
      clt wbr wo wral wrex wa c1 cfa cneg cmul aaliou3lem9 aaliou3lem6 ad2antrl
      caddc cle cn0 2nn nnnn0 faccl 3syl nnexpcl sylancr wne cc cc0 aaliou3lem5
      recnd nnne0 divcan4 syl3anc aaliou3lem7 simpld eqnetrd necomd df-ne sylib
      nncn syl aaliou3lem4 nnre remulcl syl2anc nnrp rerpdivcl resubcl 2re 2pos
      abscl elrpii peano2nn0 nnz znegcl rpexpcl rpmulcl simplr ad2antrr rpdivcl
      oveq2d fveq2d simprd eqbrtrd simprr letrd lenlt mpbid oveq1 eqeq2d notbid
      rpre wb breq2d anbi12d oveq2 rcla42ev syl112anc exp32 rexlimdv mpd pm4.56
      breq12d rexbii rexnal bitri nrexdv nrex aaliou2b mto ) CUBLCJUCZKUCZMNZUD
      ZEUCZYQDUCZUENZMNZCYRUFNZUGUHZUIUJZUKZKOULZJPULZEQUMZDOUMUUJDOUUAOLZUUIEQ
      UUKYTQLZUNZYSRZUUFRZUNZKOUMZJPUMZUUIRZUUMSSUAUCZUOVBNZUPUHZUQZUENZURNZYTS
      UUTUPUHZUENZUUAUENZMNZVCUJZUAOUMUURUAUUAYTUSUUMUVJUURUAOUUMUUTOLZUVJUURUU
      MUVKUVJUNZUNZUUTBUHZUVGURNZPLZUVGOLZCUVOUVGMNZUDZRZUVICUVRUFNZUGUHZUIUJZR
      ZUURUVKUVPUUMUVJUUTABCDEFGHIUTVAUVMSOLUVFVDLZUVQVEUVMUUTVDLZUVFOLUWEUVKUW
      FUUMUVJUUTVFVAZUUTVGUVFVFVHSUVFVIVJZUVMCUVRVKUVTUVMUVRCUVMUVRUVNCUVMUVNVL
      LUVGVLLZUVGVMVKZUVRUVNUDUVMUVNUVKUVNTLZUUMUVJUUTABCDEFGHIVNVAZVOUVMUVQUWI
      UWHUVGWEWFUVMUVQUWJUWHUVGVPWFUVNUVGVQVRZUVKUVNCVKZUUMUVJUVKUWNCUVNUFNZUGU
      HZUVEVCUJZUUTABCDEFGHIVSZVTVAWAWBCUVRWCWDUVMUWBUVIVCUJZUWDUVMUWBUVEUVIUVM
      UWAVLLUWBTLZUVMUWAUVMCTLUVRTLZUWATLABCDEFGHIWGUVMUVOTLZUVGQLZUXAUVMUWKUVG
      TLZUXBUWLUVMUVQUXDUWHUVGWHWFUVNUVGWIWJUVMUVQUXCUWHUVGWKWFUVOUVGWLWJCUVRWM
      VJVOUWAWPWFZUVMUVEQLZUVETLUVMSQLZUVDQLZUXFSWNWOWQZUVMUXGUVCPLZUXHUXIUVMUV
      BOLZUVBPLUXJUVMUWFUVAVDLUXKUWGUUTWRUVAVGVHUVBWSUVBWTVHSUVCXAVJSUVDXBVJUVE
      XQWFUVMUVIQLZUVITLZUVMUULUVHQLZUXLUUKUULUVLXCUVMUVHOLZUXNUVMUVQUUAVDLZUXO
      UWHUUKUXPUULUVLUUAVFXDUVGUUAVIWJUVHWKWFYTUVHXEWJUVIXQWFZUVMUWBUWPUVEVCUVM
      UWAUWOUGUVMUVRUVNCUFUWMXFXGUVKUWQUUMUVJUVKUWNUWQUWRXHVAXIUUMUVKUVJXJXKUVM
      UWTUXMUWSUWDXRUXEUXQUWBUVIXLWJXMUUPUVTUWDUNCUVOYQMNZUDZRZUUCCUXRUFNZUGUHZ
      UIUJZRZUNJKUVOUVGPOYPUVOUDZUUNUXTUUOUYDUYEYSUXSUYEYRUXRCYPUVOYQMXNZXOXPUY
      EUUFUYCUYEUUEUYBUUCUIUYEUUDUYAUGUYEYRUXRCUFUYFXFXGXSXPXTYQUVGUDZUXTUVTUYD
      UWDUYGUXSUVSUYGUXRUVRCYQUVGUVOMYAZXOXPUYGUYCUWCUYGUUCUVIUYBUWBUIUYGUUBUVH
      YTMYQUVGUUAUEXNXFUYGUYAUWAUGUYGUXRUVRCUFUYHXFXGYHXPXTYBYCYDYEYFUURUUHRZJP
      UMUUSUUQUYIJPUUQUUGRZKOUMUYIUUPUYJKOYSUUFYGYIUUGKOYJYKYIUUHJPYJYKWDYLYMEC
      DKJYNYO $.
      $( [20-Nov-2014] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Algebraic numbers are countable
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d H a b c d e f $.  $d R a b c d e f $.  $d S a b c d e f $.
    $d A a b c d e f $.  $d B a b c d e f $.

    $( Lemma for ~ isopo . $)
    isopolem $p |- ( H Isom R , S ( A , B ) -> ( S Po B -> R Po A ) ) $=
      ( va vb vc vd ve vf cv wbr wa wi wral wcel ex wb anbi12d wiso wpo w3a cfv
      wn wf1o isof1o f1of ffvelrn 3anim123d 3syl imp breq12 anidms notbid breq1
      wceq anbi1d imbi12d breq2 imbi1d anbi2d rcla43v syl simpl simpr1 syl12anc
      wf isorel simpr2 simpr3 sylibrd com23 imp31 ralrimivvva df-po 3imtr4g ) A
      BCDEUAZFLZVSDMZUEZVSGLZDMZWBHLZDMZNZVSWDDMZOZNZHBPGBPFBPZILZWKCMZUEZWKJLZ
      CMZWNKLZCMZNZWKWPCMZOZNZKAPJAPIAPZBDUBACUBVRWJXBVRWJNXAIJKAAAVRWJWKAQZWNA
      QZWPAQZUCZXAVRXFWJXAVRXFWJXAOVRXFNZWJWKEUDZXHDMZUEZXHWNEUDZDMZXKWPEUDZDMZ
      NZXHXMDMZOZNZXAXGXHBQZXKBQZXMBQZUCZWJXROVRXFYBVRABEUFABEVHZXFYBOABCDEUGAB
      EUHYCXCXSXDXTXEYAYCXCXSABWKEUIRYCXDXTABWNEUIRYCXEYAABWPEUIRUJUKULWIXRXJXH
      WBDMZWENZXHWDDMZOZNXJXLXKWDDMZNZYFOZNFGHXHXKXMBBBVSXHUQZWAXJWHYGYKVTXIYKV
      TXISVSXHVSXHDUMUNUOYKWFYEWGYFYKWCYDWEVSXHWBDUPURVSXHWDDUPUSTWBXKUQZYGYJXJ
      YLYEYIYFYLYDXLWEYHWBXKXHDUTWBXKWDDUPTVAVBWDXMUQZYJXQXJYMYIXOYFXPYMYHXNXLW
      DXMXKDUTVBWDXMXHDUTUSVBVCVDXGWMXJWTXQXGWLXIXGVRXCXCWLXISVRXFVEZVRXCXDXEVF
      ZYOABWKWKCDEVIVGUOXGWRXOWSXPXGWOXLWQXNXGVRXCXDWOXLSYNYOVRXCXDXEVJZABWKWNC
      DEVIVGXGVRXDXEWQXNSYNYPVRXCXDXEVKZABWNWPCDEVIVGTXGVRXCXEWSXPSYNYOYQABWKWP
      CDEVIVGUSTVLRVMVNVORFGHBDVPIJKACVPVQ $.
      $( [16-Nov-2014] $)

    $( An isomorphism preserves partial ordering. $)
    isopo $p |- ( H Isom R , S ( A , B ) -> ( R Po A <-> S Po B ) ) $=
      ( wiso wpo ccnv wi isocnv isopolem syl impbid ) ABCDEFZACGZBDGZNBADCEHZFO
      PIABCDEJBADCQKLABCDEKM $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ isoso . $)
    isosolem $p |- ( H Isom R , S ( A , B ) -> ( S Or B -> R Or A ) ) $=
      ( va vb vc vd wpo cv wbr weq w3o wral wa wcel wceq ex 3orbi123d wiso wf1o
      wor isopolem cfv wi wf isof1o f1of ffvelrn anim12d 3syl breq1 eqeq1 breq2
      imp eqeq2 rcla42v syl isorel wb f1of1 f1fveq sylan bicomd ancom2s sylibrd
      wf1 impancom ralrimivv df-so 3imtr4g ) ABCDEUAZBDJZFKZGKZDLZFGMZVPVODLZNZ
      GBOFBOZPACJZHKZIKZCLZHIMZWDWCCLZNZIAOHAOZPBDUCACUCVMVNWBWAWIABCDEUDVMWAWI
      VMWAPWHHIAAVMWCAQZWDAQZPZWAWHVMWLPZWAWCEUEZWDEUEZDLZWNWORZWOWNDLZNZWHWMWN
      BQZWOBQZPZWAWSUFVMWLXBVMABEUBZABEUGZWLXBUFABCDEUHZABEUIXDWJWTWKXAXDWJWTAB
      WCEUJSXDWKXAABWDEUJSUKULUPVTWSWNVPDLZWNVPRZVPWNDLZNFGWNWOBBVOWNRVQXFVRXGV
      SXHVOWNVPDUMVOWNVPUNVOWNVPDUOTVPWORXFWPXGWQXHWRVPWOWNDUOVPWOWNUQVPWOWNDUM
      TURUSWMWEWPWFWQWGWRABWCWDCDEUTWMWQWFVMABEVHZWLWQWFVAVMXCXIXEABEVBUSABWCWD
      EVCVDVEVMWKWJWGWRVAABWDWCCDEUTVFTVGVIVJSUKFGBDVKHIACVKVL $.
      $( [16-Nov-2014] $)

    $( An isomorphism preserves strict ordering. $)
    isoso $p |- ( H Isom R , S ( A , B ) -> ( R Or A <-> S Or B ) ) $=
      ( wiso wor ccnv wi isocnv isosolem syl impbid ) ABCDEFZACGZBDGZNBADCEHZFO
      PIABCDEJBADCQKLABCDEKM $.
      $( [16-Nov-2014] $)

    $d a b c d e f x $.
    $( The complex numbers can be linearly ordered. $)
    cnso $p |- E. x x Or CC $=
      ( va vb vd vc ve cr cc cv wex wor wbr cn cnex cfv wceq wa clt wrex syl wb
      wf1o cen cpw nnex pwex rpnnen cpnnen entr4i bren mpbi copab cxp ltso wiso
      cin eqid f1oiso mpan2 isoso soinxp syl6bb mpbii xpex inex2 cla4ev exlimiv
      soeq1 ax-mp ) GHBIZUBZBJZHAIZKZAJZGHUCLVLGMUDHMUEUFUGUHUIGHBNUJUKVKVOBVKH
      CIDIZVJOPEIFIZVJOPQVPVQRLQFGSDGSCEULZHHUMZUPZKZVOVKGRKZWAUNVKGHRVRVJUOZWB
      WAUAVKVRVRPWCVRUQDFCEGHRVRVJURUSWCWBHVRKWAGHRVRVJUTHVRVAVBTVCVNWAAVTVSVRH
      HNNVDVEHVMVTVHVFTVGVI $.
      $( [16-Nov-2014] $)

    $d a b c F $.
    $( A well-ordering has no nontrivial automorphisms.  (Is sethood actually
       needed here?) $)
    weniso $p |- ( ( A e. V /\ R We A /\ F Isom R , R ( A , A ) ) ->
        F = ( _I |` A ) ) $=
      ( va vc vb wcel cvv wceq cfv wral wn wbr wa syl wi fveq2 id adantr wwe cv
      wiso cid cres elex w3a crab c0 wne wrex rabn0 rexnal bitri wfr wss simpl1
      rabexg simpl2 wefr ssrab2 a1i simpr fri syl22anc weq eqeq12d notbid elrab
      ex ralrab con34b bicomi ralbii wo simprr wor weso wf1o simpl3 isof1o f1of
      wb wf simprl ffvelrn syl2anc sotrieq syl12anc con2bid mpbird breq1 rcla4v
      imbi12d com23 imp wf1 f1fveq pm2.21 ad2antll sylbid syld ccnv f1ocnv 3syl
      f1of1 isorel f1ocnvfv2 breq1d bitr2d biimpa simplrr adantl fveq2d 3eqtr3d
      sylc jaodan syl5bi rexlimdv syl5bir pm2.18d fvresi eqeq2d biimprd ralimia
      mpdan wfn 3ad2ant3 f1ofn fnresi eqfnfv2 syl3an1 ) ADHAIHZABUAZAABBCUCZCUD
      AUEZJZADUFYMYNYOUGZYQEUBZCKZYSYPKZJZEALZYRYTYSJZEALZUUCYRUUEUUEMZUUDMZEAU
      HZUIUJZYRUUEUUIUUGEAUKUUFUUGEAULUUDEAUMUNYRUUIFUBZGUBZBNZMZFUUHLZGUUHUKZU
      UEYRUUIUUOYRUUIOZUUHIHZABUOZUUHAUPZUUIUUOUUPYMUUQYMYNYOUUIUQUUGEAIURPUUPY
      NUURYMYNYOUUIUSABUTPUUSUUPUUGEAVAVBYRUUIVCGFAUUHIBVDVEVJYRUUNUUEGUUHUUKUU
      HHUUKAHZUUKCKZUUKJZMZOZYRUUNUUEQZUUGUVCEUUKAEGVFZUUDUVBUVFYTUVAYSUUKYSUUK
      CRUVFSVGVHVIYRUVDUVEUUNUULUUJCKZUUJJZQZFALZYRUVDOZUUEUUNUVHMZUUMQZFALUVJU
      UGUVLUUMFEAEFVFZUUDUVHUVNYTUVGYSUUJYSUUJCRUVNSVGVHVKUVMUVIFAUVIUVMUULUVHV
      LVMVNUNUVKUVAUUKBNZUUKUVABNZVOZUVJUUEQZUVKUVQUVCYRUUTUVCVPUVKUVBUVQUVKABV
      QZUVAAHZUUTUVBUVQMWCUVKYNUVSYMYNYOUVDUSABVRPUVKAACWDZUUTUVTUVKAACVSZUWAUV
      KYOUWBYMYNYOUVDVTZAABBCWAZPZAACWBPYRUUTUVCWEZAAUUKCWFWGZUWFAUVAUUKBWHWIWJ
      WKUVKUVOUVRUVPUVKUVOOUVJUVACKZUVAJZUUEUVKUVOUVJUWIQUVKUVJUVOUWIUVKUVTUVJU
      VOUWIQZQUWGUVIUWJFUVAAUUJUVAJZUULUVOUVHUWIUUJUVAUUKBWLUWKUVGUWHUUJUVAUUJU
      VACRUWKSVGWNWMPWOWPUVKUWIUUEQUVOUVKUWIUVBUUEUVKAACWQZUVTUUTUWIUVBWCUVKUWB
      UWLUWEAACXFPUWGUWFAAUVAUUKCWRWIUVCUVBUUEQYRUUTUVBUUEWSZWTXATXBUVKUVPOZUVJ
      UUKCXCZKZCKZUWPJZUUEUWNUWPAHZUWPUUKBNZUVJUWRQUVKUWSUVPUVKAAUWOWDZUUTUWSUV
      KUWBAAUWOVSUXAUWEAACXDAAUWOWBXEUWFAAUUKUWOWFWGZTUVKUVPUWTUVKUWTUWQUVABNZU
      VPUVKYOUWSUUTUWTUXCWCUWCUXBUWFAAUWPUUKBBCXGWIUVKUWQUUKUVABUVKUWBUUTUWQUUK
      JZUWEUWFAAUUKCXHWGZXIXJXKUWSUVJUWTUWRUVIUWTUWRQFUWPAUUJUWPJZUULUWTUVHUWRU
      UJUWPUUKBWLUXFUVGUWQUUJUWPUUJUWPCRUXFSVGWNWMWOXPUVKUWRUUEQUVPUVKUWRUUEUVK
      UWROZUVCUVBUUEYRUUTUVCUWRXLUXGUWQCKZUWQUVAUUKUWRUXHUWQJUVKUWQUWPCRXMUVKUX
      HUVAJUWRUVKUWQUUKCUXEXNTUVKUXDUWRUXETXOUWMXPVJTXBXQYFXRVJXRXSXBXTYAUUDUUB
      EAYSAHZUUBUUDUXIUUAYSYTAYSYBYCYDYEPYRCAYGZYPAYGZYQUUCWCYRUWBUXJYOYMUWBYNU
      WDYHAACYIPUXKYRAYJVBEACYPYKWGWKYL $.
      $( [16-Nov-2014] $)

    $d a b c f R $.  $d f A $.
    $( A finite totally ordered set has a unique order isomorphism to a finite
       ordinal. $)
    finnisoeu $p |- ( ( R Or A /\ A e. Fin ) ->
        E! f f Isom _E , R ( ( card ` A ) , A ) ) $=
      ( va cfn wcel ccrd cep wiso con0 syl wceq cen wbr wf1o isof1o adantl ccom
      wa a1i wor cfv cv wex weq wi wal weu wrex wreu simpr wofi ordtype syl2anc
      wwe reurex simprr vex f1oen ficardid ensymg mpd entr syl2anr com ficardom
      simprl ad2antlr onomeneq mpbid isoeq4 expr eximdv rexlimdva cid cres ccnv
      wb cvv fvex word cardon eloni ordwe id isocnv isotr weniso syl3anc coeq2d
      mp2b coass adantr f1ococnv2 coeq1d syl5eqr eqtr3d f1of fcoi1 3eqtr3d gen2
      wf fcoi2 isoeq1 eu4 sylanbrc ) ABUAZAEFZSZAGUBZAHBCUCZIZCUDZXLXJAHBDUCZIZ
      SZCDUEUFZDUGCUGZXLCUHXIXNAHBXKIZCUDZDJUIZXMXIXTDJUJZYAXIXHABUOYBXGXHUKABU
      LDAEBCUMUNXTDJUPKXIXTXMDJXIXNJFZSXSXLCXIYCXSXLXIYCXSSZSZXSXLXIYCXSUQYEXNX
      JLZXSXLVRYEXNXJMNZYFYDXNAMNZAXJMNZYGXIXSYHYCXSXNAXKOYHXNAHBXKPXNAXKDURUSK
      QXHYIXGXHXJAMNYIAUTXJAEVAVBQXNAXJVCVDYEYCXJVEFZYGYFVRXIYCXSVGXHYJXGYDAVFV
      HXNXJVIUNVJXNAXJHBXKVKKVJVLVMVNVBXRXIXQCDXPXKVOXJVPZRZVOAVPZXNRZXKXNXPXKX
      KVQZXNRZRZYLYNXPYPYKXKXPXJVSFZXJHUOZXJXJHHYPIZYPYKLYRXPAGVTTYSXPXJJFXJWAY
      SAWBXJWCXJWDWKTXOXOAXJBHYOIYTXLXOWEXJAHBXKWFXJAXJHBHYOXNWGVDXJHYPVSWHWIWJ
      XPYQXKYORZXNRYNXKYOXNWLXPUUAYMXNXPXJAXKOZUUAYMLXLUUBXOXJAHBXKPZWMXJAXKWNK
      WOWPWQXPXJAXKXBZYLXKLXLUUDXOXLUUBUUDUUCXJAXKWRKWMXJAXKWSKXPXJAXNXBZYNXNLX
      OUUEXLXOXJAXNOUUEXJAHBXNPXJAXNWRKQXJAXNXCKWTXATXLXOCDXJAHBXNXKXDXEXF $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d A a b c d e f g h i j k $.  $d B a b c d e f g h i j k $.

    $( Countability of a countable union of finite sets with an strict (not
       globally well) order fulfilling the choice role. $)
    iunfictbso $p |- ( ( A ~<_ om /\ A C_ Fin /\ B Or U. A ) ->
        U. A ~<_ om ) $=
      ( va vf vg vh vc com cdom wbr c0 wceq cv wcel wa syl cfv cep wiso syl2anc
      vb vd ve vi vj cfn wss cuni wor w3a 0dom breq1 mpbiri a1d wne wex wfo cvv
      wi n0 csdm omex a1i ne0i unieq uni0 syl6eq necon3i adantl simpl1 brrelexi
      reldom 0sdomg 3syl mpbird fodomr syl3anc cxp cen con0 wrex ccrd cio cmpt2
      wb cif omelon onenon ax-mp xpnum mp2an wf wral simplrr fof simprl ffvelrn
      co adantr elssuni wf1o weu cab simpll3 soss sylc simpll2 sseldd finnisoeu
      iotacl iotaex isoeq1 cbvabv elab2 biimpi isof1o sylan ad2antrr ralrimivva
      f1of wn ifclda eqid fmpt2 sylib wel eluni simprr foelrn ccnv simprrl word
      ordom ficardom fveq2 eqidd ifbieq12d expr mpd exlimdv ordelss sylancr weq
      f1ocnv simprll simprrr eleqtrd fveq2d eleq2d isoeq4 isoeq5 bitrd iotabidv
      fveq1d eleq1 fvex vex ifex ovmpt2 iftrue f1ocnvfv2 3eqtrrd rcla4eov exp3a
      rexlimdv syl5bi ralrimiv foov sylanbrc xpex fodomnum mpsyl xpomen domentr
      ex sylancl expcom exlimiv sylbi pm2.61ine ) AHIJZAUFUGZAUHZBUIZUJZUWCHIJZ
      USZUWCKUWCKLZUWFUWEUWHUWFKHIJHUKUWCKHIULUMUNUWCKUOZCMZUWCNZCUPUWGCUWCUTUW
      KUWGCUWEUWKUWFUWEUWKOZHAUAMZUQZUAUPZUWFUWLHURNZKAVAJZUWAUWOUWPUWLVBVCUWLU
      WQAKUOZUWKUWRUWEUWKUWIUWRUWCUWJVDAKUWCKAKLUWCKUHKAKVEVFVGVHPVIUWLUWAAURNU
      WQUWRWEUWAUWBUWDUWKVJZAHIVLVKAURVMVNVOUWSHAURUAVPVQUWLUWNUWFUAUWEUWKUWNUW
      FUWEUWKUWNOZOZUWCHHVRZIJZUXBHVSJUWFUWJUXBVSJCVTWAZUXAUXBUWCDEHHEMZDMZUWMQ
      ZWBQZNZUXEUXHUXGRBFMZSZFWCZQZUWJWFZWDZUQZUXCUWJHVSJCVTWAZUXQUXDHVTNUXQWGC
      HWHWIZUXRCHHWJWKUXAUXBUWCUXOWLZGMZUBMUCMUXOWRLUCHWAUBHWAZGUWCWMUXPUXAUXNU
      WCNZEHWMDHWMUXSUXAUYBDEHHUXAUXFHNZUXEHNZOZOZUXIUXMUWJUWCUYFUXIOZUXGUWCUXM
      UYGUXGANZUXGUWCUGZUYFUYHUXIUYFHAUWMWLZUYCUYHUYFUWNUYJUWEUWKUWNUYEWNHAUWMW
      OZPUXAUYCUYDWPHAUXFUWMWQTZWSUXGAWTZPUYFUXHUXGUXLWLZUXIUXMUXGNUYFUXHUXGRBU
      XLSZUXHUXGUXLXAUYNUYFUXKFXBZUXLUXKFXCZNZUYOUYFUXGBUIZUXGUFNUYPUYFUYIUWDUY
      SUYFUYHUYIUYLUYMPUWAUWBUWDUWTUYEXDUXGUWCBXEXFUYFAUFUXGUWAUWBUWDUWTUYEXGUY
      LXHUXGBFXITUXKFXJUYRUYOUXHUXGRBUWJSZUYOCUXLUYQUXKFXKUXHUXGRBUXLUWJXLUXKUY
      TFCUXHUXGRBUWJUXJXLXMXNXOVNUXHUXGRBUXLXPUXHUXGUXLXTVNUXHUXGUXEUXLWQXQXHUX
      AUWKUYEUXIYAUWEUWKUWNWPXRYBXSDEHHUXNUWCUXOUXOYCZYDYEUXAUYAGUWCUXTUWCNGUDY
      FZUDMZANZOZUDUPUXAUYAUDUXTAYGUXAVUEUYAUDUXAVUEUYAUXAVUEOZVUCUEMZUWMQZLZUE
      HWAZUYAVUFUWNVUDVUJUWEUWKUWNVUEWNUXAVUBVUDYHUEHAVUCUWMYITVUFVUIUYAUEHVUFV
      UGHNZVUIUYAUXAVUEVUKVUIOZUYAUXAVUEVULOZOZVUKUXTVUHWBQZVUHRBUXJSZFWCZYJZQZ
      HNZUXTVUGVUSUXOWRZLUYAUXAVUEVUKVUIYKZVUNVUOHVUSVUNHYLVUOHNZVUOHUGYMVUNVUH
      UFNZVVCVUNAUFVUHUWAUWBUWDUWTVUMXGVUNUYJVUKVUHANZVUNUWNUYJUWEUWKUWNVUMWNUY
      KPVVBHAVUGUWMWQTZXHZVUHYNPHVUOUUAUUBVUNVUHVUOVURWLZUXTVUHNZVUSVUONZVUNVUO
      VUHVUQXAZVUHVUOVURXAVVHVUNVUOVUHRBVUQSZVVKVUNVUPFXBZVUQVUPFXCZNZVVLVUNVUH
      BUIZVVDVVMVUNVUHUWCUGZUWDVVPVUNVVEVVQVVFVUHAWTPUWAUWBUWDUWTVUMXDVUHUWCBXE
      XFVVGVUHBFXITVUPFXJVVOVVLVUOVUHRBUWJSZVVLCVUQVVNVUPFXKVUOVUHRBVUQUWJXLVUP
      VVRFCVUOVUHRBUWJUXJXLXMXNXOVNVUOVUHRBVUQXPPZVUOVUHVUQUUDVUHVUOVURXTVNVUNU
      XTVUCVUHUXAVUBVUDVULUUEUXAVUEVUKVUIUUFUUGZVUHVUOUXTVURWQTZXHZVUNVVAVVJVUS
      VUQQZUWJWFZVWCUXTVUNVUKVUTVVAVWDLVVBVWBDEVUGVUSHHUXNVWDUXOUXEVUONZUXEVUQQ
      ZUWJWFDUEUUCZUXIVWEUXMUWJVWFUWJVWGUXHVUOUXEVWGUXGVUHWBUXFVUGUWMYOZUUHZUUI
      VWGUXEUXLVUQVWGUXKVUPFVWGUXKVUOUXGRBUXJSZVUPVWGUXHVUOLUXKVWJWEVWIUXHUXGVU
      ORBUXJUUJPVWGUXGVUHLVWJVUPWEVWHVUOUXGVUHRBUXJUUKPUULUUMUUNVWGUWJYPYQUXEVU
      SLZVWEVVJVWFUWJVWCUWJUXEVUSVUOUUOUXEVUSVUQYOVWKUWJYPYQVUAVVJVWCUWJVUSVUQU
      UPCUUQUURUUSTVUNVVJVWDVWCLVWAVVJVWCUWJUUTPVUNVVKVVIVWCUXTLVVSVVTVUOVUHUXT
      VUQUVATUVBUBUCHHVUGVUSUXTUXOUVCVQYRUVDUVEYSUVOYTUVFUVGUBUCGHHUWCUXOUVHUVI
      CUXBUWCUXOHHVBVBUVJUVKUVLUVMUWCUXBHUVNUVPYRYTYSUVQUVRUVSUVT $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d A a b c d e f g h i $.
    aannenlem.a $e |- H = ( a e. NN0 |-> { b e. CC | E. c e.
        { d e. ( Poly ` ZZ ) | ( d =/= 0p /\ ( deg ` d ) <_ a /\
            A. e e. NN0 ( abs ` ( ( coeff ` d ) ` e ) ) <_ a ) }
      ( c ` b ) = 0 } ) $.
    $( Lemma for ~ aannen . $)
    aannenlem1 $p |- ( A e. NN0 -> ( H ` A ) e. Fin ) $=
      ( cn0 wcel cfv cc0 wceq cle wbr ccoe cz cc cfn wa c0p cdgr cabs wral cply
      wne w3a crab wrex breq2 ralbidv 3anbi23d rabbidv rexeqdv cnex rabex fvmpt
      cv ciun iunrab cneg cfz co cmap cdom fzfi mapfi mp2an a1i fvex cres neeq1
      cvv weq fveq2 breq1d fveq1d fveq2d 3anbi123d elrab simp3 anim2i sylbi wss
      wf wfn crn 0z coef2 mpan2 ad2antrl ffn syl cr wb adantl ffvelrn sylan zre
      eqid nn0re ad2antrr absle syl2anc nn0z znegcl elfz bitr4d biimpd ralimdva
      syl3anc impr fnfvrnss df-f elfznn0 ssriv fssres sylancl ovex elmap sylibr
      sylanbrc syl5 simp2 plyf 3syl simplrl cmul csu simplrr adantr fvres 3expa
      ex cuz dgrcl eluz mpbird coeid3 eqeltrd simplll cexp 3eqtr3d oveq1d simpr
      simp1ll simpllr simp1rl 3eqtr4d eqfnfvd expr reseq1d impbid1 expcom dom2d
      sumeq2dv syl2ani mpi domfi simp1 wi ccnv csn cima fniniseg syl6rbbr eqrdv
      eqeq1d chash fta1 simpld ralrimiv iunfi syl5eqelr ) AIJZACKEURZFURZKZLMZF
      GURZUAUFZUVTUBKZANOZBURZUVTPKZKZUCKZANOZBIUDZUGZGQUEKZUHZUIZERUHZSDAUVSFU
      WAUWBDURZNOZUWGUWONOZBIUDZUGZGUWKUHZUIZERUHUWNICUWOAMZUXAUWMERUXBUVSFUWTU
      WLUXBUWSUWJGUWKUXBUWPUWCUWRUWIUWAUWOAUWBNUJUXBUWQUWHBIUWOAUWGNUJUKULUMUNU
      MHUWMERUOUPUQUVOUWNFUWLUVSERUHZUSZSUVSFEUWLRUTUVOUWLSJZUXCSJZFUWLUDUXDSJU
      VOAVAZAVBVCZLAVBVCZVDVCZSJZUWLUXJVEOZUXEUXKUVOUXHSJUXISJUXKUXGAVFLAVFUXHU
      XIVGVHVIUVOUWLVMJUXLUWJGUWKQUEVJUPUVODEUWLUXJUWOPKZUXIVKZUVPPKZUXIVKZVMUW
      OUWLJZUWOUWKJZUWDUXMKZUCKZANOZBIUDZTZUVOUXNUXJJZUXQUXRUWOUAUFZUWOUBKZANOZ
      UYBUGZTZUYCUWJUYHGUWOUWKGDVNZUWAUYEUWCUYGUWIUYBUVTUWOUAVLUYJUWBUYFANUVTUW
      OUBVOVPUYJUWHUYABIUYJUWGUXTANUYJUWFUXSUCUYJUWDUWEUXMUVTUWOPVOVQVRVPUKVSVT
      ZUYHUYBUXRUYEUYGUYBWAWBWCUVOUYCUYDUVOUYCTZUXIUXHUXNWEZUYDUYLIUXHUXMWEZUXI
      IWDUYMUYLUXMIWFZUXMWGUXHWDZUYNUYLIQUXMWEZUYOUXRUYQUVOUYBUXRLQJZUYQWHUXMQU
      WOUXMWTZWIWJZWKIQUXMWLWMZUYLUYOUXSUXHJZBIUDZUYPVUAUVOUXRUYBVUCUVOUXRTZUYA
      VUBBIVUDUWDIJZTZUYAVUBVUFUYAUXGUXSNOUXSANOTZVUBVUFUXSWNJZAWNJZUYAVUGWOVUF
      UXSQJZVUHVUDUYQVUEVUJUXRUYQUVOUYTWPIQUWDUXMWQWRZUXSWSWMUVOVUIUXRVUEAXAXBU
      XSAXCXDVUFVUJUXGQJZAQJZVUBVUGWOVUKVUFVUMVULUVOVUMUXRVUEAXEZXBZAXFWMVUOUXS
      UXGAXGXKXHXIXJXLBIUXHUXMXMXDIUXHUXMXNYBDUXIIUWOAXOXPIUXHUXIUXMXQXRUXHUXIU
      XNUXGAVBXSLAVBXSXTYAYNYCUXQUVOUXRUYGTZUVPUWKJZUVPUBKZANOZTZUXNUXPMZDEVNZW
      OZUVPUWLJZUXQUYIVUPUYKUYHUYGUXRUYEUYGUYBYDWBWCVVDVUQUVPUAUFZVUSUWDUXOKZUC
      KZANOZBIUDZUGZTVUTUWJVVJGUVPUWKGEVNZUWAVVEUWCVUSUWIVVIUVTUVPUAVLVVKUWBVUR
      ANUVTUVPUBVOVPVVKUWHVVHBIVVKUWGVVGANVVKUWFVVFUCVVKUWDUWEUXOUVTUVPPVOVQVRV
      PUKVSVTVVJVUSVUQVVEVUSVVIYDWBWCVUPVUTTZUVOVVCVVLUVOTVVAVVBVVLUVOVVAVVBVVL
      UVOVVATZTZFRUWOUVPVVNUXRRRUWOWEUWORWFUXRUYGVUTVVMUUAQUWOYERRUWOWLYFVVNVUQ
      RRUVPWEUVPRWFVUPVUQVUSVVMYGQUVPYERRUVPWLYFVVNUVQRJZTZUXIUVTUXMKZUVQUVTUUB
      VCZYHVCZGYIZUXIUVTUXOKZVVRYHVCZGYIZUVQUWOKZUVQUVPKZVVPUXIVVSVWBGVVPUVTUXI
      JZTZVVQVWAVVRYHVWGUVTUXNKZUVTUXPKZVVQVWAVWGUVTUXNUXPVVPVVAVWFVVLUVOVVAVVO
      YJYKVQVWFVWHVVQMVVPUVTUXIUXMYLWPVWFVWIVWAMVVPUVTUXIUXOYLWPUUCUUDUUPVVPUXR
      AUYFYOKJZVVOVWDVVTMVVLVVMVVOUXRUXRUYGVUTVVMVVOUUFYMZVVPVWJUYGVVNUYGVVOUXR
      UYGVUTVVMUUGYKVVPUYFQJZVUMVWJUYGWOVVPUXRUYFIJVWLVWKQUWOYPUYFXEYFVVPUVOVUM
      VVLUVOVVAVVOYGVUNWMZUYFAYQXDYRVVNVVOUUEZUXMQGUWOAUYFUVQUYSUYFWTYSXKVVPVUQ
      AVURYOKJZVVOVWEVWCMVVLVVMVVOVUQVUQVUSVUPVVMVVOUUHYMZVVPVWOVUSVVNVUSVVOVUP
      VUQVUSVVMYJYKVVPVURQJZVUMVWOVUSWOVVPVUQVURIJVWQVWPQUVPYPVURXEYFVWMVURAYQX
      DYRVWNUXOQGUVPAVURUVQUXOWTVURWTYSXKUUIUUJUUKVVBUXMUXOUXIUWOUVPPVOUULUUMUU
      NUUQUUOUURUXJUWLUUSXDUVOUXFFUWLUVQUWLJZUVQUWKJZUVQUAUFZTZUVOUXFVWRVWSVWTU
      VQUBKZANOZUWDUVQPKZKZUCKZANOZBIUDZUGZTVXAUWJVXIGUVQUWKGFVNZUWAVWTUWCVXCUW
      IVXHUVTUVQUAVLVXJUWBVXBANUVTUVQUBVOVPVXJUWHVXGBIVXJUWGVXFANVXJUWFVXEUCVXJ
      UWDUWEVXDUVTUVQPVOVQVRVPUKVSVTVXIVWTVWSVWTVXCVXHUUTWBWCVXAUXFUVAUVOVXAUXC
      UVQUVBLUVCUVDZSVXADUXCVXKVXAUWOVXKJZUWORJUWOUVQKZLMZTZUWOUXCJVXAUVQRWFZUY
      RVXLVXOWOVWSVXPVWTVWSRRUVQWEVXPQUVQYERRUVQWLWMYKWHRLUWOUVQQUVEXRUVSVXNEUW
      OREDVNUVRVXMLUVPUWOUVQVOUVHVTUVFUVGVXAVXKSJVXKUVIKVXBNOVXKQUVQVXKWTUVJUVK
      YTVIYCUVLFUWLUXCUVMXDUVNYT $.
      $( [16-Nov-2014] $)

    $( Lemma for ~ aannen . $)
    aannenlem2 $p |- AA = U. ran H $=
      ( vf vg vh cv cfv cc0 wceq cle wbr cn0 wrex wcel wa caa c0p wne cdgr ccoe
      vi cabs wral w3a cz cply crab cc cab cuni crn csn cdif wel wex wi cpr cfz
      cun cxr clt csup simp3 eldifi adantr 3adant2 eldifsn simprbi wss 0nn0 a1i
      co dgrcl syl elexi fvex prss biimpi syl2anc ssrab2 unssd cr nn0ssre sstri
      ressxr syl6ss prid2 elun1 ax-mp supxrub sylancl fveq2 abs0 prid1 syl6eqel
      syl6eq adantl wf 0z eqid coef2 sylan nn0abscl simplr ad2antrr simpr dgrub
      ffvelrn syl3anc cvv wb elfz2nn0 syl3anbrc weq fveq2d eqeq2d rcla4ev eqeq1
      rexbidv elrab sylanbrc elun2 pm2.61dane ralrimiva breq1d 3anbi123d eqeq1d
      ralbidv cfn mp2an breq2 rabbidv eleq2 impcom anim2i neeq1 fveq1d simp2 c0
      3jca fveq1 prfi fzfi abrexfi cin dfrab2 eqsstri ssfi unfi ne0i wor xrltso
      inss1 fisup2g mpan sseldd eqidd 3anbi23d rexeqdv cnex anbi12d cla4ev 3exp
      rabex rexlimiv simp1 3imtr4i ssriv ssrexv cbvrexv syl6ib syl6bi rexlimivw
      sylbi exlimiv impbii elaa eluniab 3bitr4i eqriv rnmpt unieqi eqtr4i ) UAH
      KZDKZEKZLZMNZEFKZUBUCZUWNUDLZCKZOPZAKZUWNUELZLZUGLZUWQOPZAQUHZUIZFUJUKLZU
      LZRZDUMULZNZCQRZHUNZUOZBUPZUOIUAUXMIKZUMSZUXOJKZLZMNZJUXFUBUQZURZRZTZIHUS
      ZUXKTZHUTZUXOUASUXOUXMSUYCUYFUYBUXPUYFUXSUXPUYFVAJUYAUXQUYASZUXSUXPUYFUYG
      UXSUXPUIZUXOUWMEUWOUWPMUXQUDLZVBZUXOUFKZUXQUELZLZUGLZNZUFMUYIVCVQZRZIQULZ
      VDZVEVFVGZOPZUXBUYTOPZAQUHZUIZFUXFULZRZDUMULZSZVUGUXINZCQRZUYFUYHUXPUXOUW
      KLZMNZEVUERZVUHUYGUXSUXPVHUYHUXQVUESZUXSVUMUYHUXQUXFSZUXQUBUCZUYIUYTOPZUW
      SUYLLZUGLZUYTOPZAQUHZUIZVUNUYGUXPVUOUXSUYGVUOUXPUXQUXFUXTVIVJZVKUYGUXPVVB
      UXSUYGUXPTZVUPVUQVVAUYGVUPUXPUYGVUOVUPUXQUXFUBVLZVMVJVVDUYSVEVNZUYIUYSSZV
      UQVVDUYSQVEVVDUYJUYRQVVDMQSZUYIQSZUYJQVNZVVHVVDVOVPVVDVUOVVIVVCUJUXQVRVSZ
      VVHVVITVVJMUYIQMQVOVTZUXQUDWAZWBWCWDUYRQVNVVDUYQIQWEVPWFZQWGVEWHWJWIWKZUY
      IUYJSVVGMUYIVVMWLUYIUYJUYRWMWNZUYSUYIWOWPVVDVUTAQVVDUWSQSZTZVVFVUSUYSSZVU
      TVVDVVFVVQVVOVJVVRVVSVURMVURMNZVVSVVRVVTVUSMUYSVVTVUSMUGLMVURMUGWQWRXAMUY
      JSMUYSSMUYIVVLWSMUYJUYRWMWNWTXBVVRVURMUCZTZVUSUYRSZVVSVWBVUSQSZVUSUYNNZUF
      UYPRZVWCVVRVWDVWAVVRVURUJSZVWDVVDQUJUYLXCZVVQVWGVVDVUOMUJSVWHVVCXDUYLUJUX
      QUYLXEZXFWPQUJUWSUYLXMXGVURXHVSVJVWBUWSUYPSZVUSVUSNZVWFVWBVVQVVIUWSUYIOPZ
      VWJVVDVVQVWAXIZVVDVVIVVQVWAVVKXJVWBVUOVVQVWAVWLVVDVUOVVQVWAVVCXJVWMVVRVWA
      XKUYLUJUXQUWSUYIVWIUYIXEXLXNUYIXOSVWJVVQVVIVWLUIXPVVMXOUWSUYIXQWNXRVUSXEV
      WEVWKUFUWSUYPUFAXSZUYNVUSVUSVWNUYMVURUGUYKUWSUYLWQXTYAYBWPUYQVWFIVUSQUXOV
      USNUYOVWEUFUYPUXOVUSUYNYCYDYEYFVUSUYRUYJYGVSYHUYSVUSWOWDYIUUEVKVUDVVBFUXQ
      UXFFJXSZUWOVUPVUAVUQVUCVVAUWNUXQUBUUAZVWOUWPUYIUYTOUWNUXQUDWQZYJVWOVUBVUT
      AQVWOUXBVUSUYTOVWOUXAVURUGVWOUWSUWTUYLUWNUXQUEWQUUBXTZYJYMYKYEYFUYGUXSUXP
      UUCVULUXSEUXQVUEEJXSVUKUXRMUXOUWKUXQUUFYLZYBWDVUFVUMDUXOUMDIXSZUWMVULEVUE
      VWTUWLVUKMUWJUXOUWKWQYLZYDYEYFUYHUYTQSZVUGVUGNZVUJUYGUXPVXBUXSVVDUYSQUYTV
      VNVVDUYSYNSZUYSUUDUCZVVFUYTUYSSZVXDVVDUYJYNSUYRYNSZVXDMUYIUUGUYQIUNZYNSZU
      YRVXHVNVXGUYPYNSVXIMUYIUUHUFIUYPUYNUUIWNUYRVXHQUUJVXHUYQIQUUKVXHQUURUULVX
      HUYRUUMYOUYJUYRUUNYOVPVXEVVDVVGVXEVVPUYSUYIUUOWNVPVVOVEVFUUPVXDVXEVVFUIVX
      FUUQVEUYSVFUUSUUTXNUVAVKUYHVUGUVBVUIVXCCUYTQUWQUYTNZUXIVUGVUGVXJUXHVUFDUM
      VXJUWMEUXGVUEVXJUXEVUDFUXFVXJUWRVUAUXDVUCUWOUWQUYTUWPOYPVXJUXCVUBAQUWQUYT
      UXBOYPYMUVCYQUVDYQYAYBWDUYEVUHVUJTHVUGVUFDUMUVEUVIUWIVUGNZUYDVUHUXKVUJUWI
      VUGUXOYRVXKUXJVUICQUWIVUGUXIYCYDUVFUVGWDUVHUVJYSUYEUYCHUXKUYDUYCUXJUYDUYC
      VACQUXJUYDUXOUXISZUYCUWIUXIUXOYRVXLUXPVULEUXGRZTUYCUXHVXMDUXOUMVWTUWMVULE
      UXGVXAYDYEVXMUYBUXPUXGUYAVNZVXMUYBVAJUXGUYAVUOVUPUYIUWQOPZVUSUWQOPZAQUHZU
      IZTVUOVUPTUXQUXGSUYGVXRVUPVUOVUPVXOVXQUVKYTUXEVXRFUXQUXFVWOUWOVUPUWRVXOUX
      DVXQVWPVWOUWPUYIUWQOVWQYJVWOUXCVXPAQVWOUXBVUSUWQOVWRYJYMYKYEVVEUVLUVMVXNV
      XMVULEUYARUYBVULEUXGUYAUVNVULUXSEJUYAVWSUVOUVPWNYTUVSUVQUVRYSUVTUWAUXOJUW
      BUXKHUXOUWCUWDUWEUXNUXLCHQUXIBGUWFUWGUWH $.
      $( [16-Nov-2014] $)

    $d H f g $.
    $( Lemma for ~ aannen . $)
    $( The algebraic numbers are countable. $)
    aannenlem3 $p |- AA ~~ NN $=
      ( vf caa cn cdom wbr cen com cc cv cfn cn0 wcel cfv wor wex cnso crn cuni
      vg aannenlem2 wss con0 wrex omelon omex nn0ennn nnenom entri ensymi breq1
      wfo rcla4ev wfn cc0 wceq c0p wne cdgr cle ccoe cabs wral w3a cz cply crab
      mp2an cvv fnmpt cnex rabex a1i mprg dffn4 mpbi nn0ex fodomnum mp2 domentr
      wb fvelrnb ax-mp aannenlem1 eleq1 syl5ibcom rexlimiv sylbi ssriv eqsstr3i
      wi aasscn soss iunfictbso syl3anc syl5eqbr exlimiv nnex nnssq qssaa sstri
      cq ssdomg sbth ) IJKLZJIKLZIJMLINKLZNJMLXKOHPZUAZHUBXMHUCXOXMHXOIBUDZUEZN
      KABCDEFGUGZXOXPNKLZXPQUHZXQXNUAZXQNKLXSXOXPRKLZRNMLXSCPZRMLZCUIUJZRXPBURZ
      YBNUISNRMLZYEUKRNULRJNUMUNUOZUPYDYGCNUIYCNRMUQUSVNBRUTZYFDPEPTVAVBEFPZVCV
      DYJVETYCVFLAPYJVGTTVHTYCVFLARVIVJFVKVLTVMUJZDOVMZVOSZYICRCRYLBVOGVPYMYCRS
      YKDOVQVRVSVTZRBWAWBCRXPBWCWDWEYHXPRNWFVNVSXTXOHXPQXNXPSZUFPZBTZXNVBZUFRUJ
      ZXNQSZYIYOYSWGYNUFRXNBWHWIYRYTUFRYPRSYQQSYRYTYPABCDEFGWJYQXNQWKWLWMWNWOVS
      XQOUHXOYAWQXQIOXRWRWPXQOXNWSWIXPXNWTXAXBXCWIJNULUNUPINJWFVNJVOSJIUHXLXDJX
      HIXEXFXGJIVOXIWEIJXJVN $.
      $( [16-Nov-2014] $)
  $}

  ${
    $d a b c d e $.
    $( The algebraic numbers are countable. $)
    aannen $p |- AA ~~ NN $=
      ( ve va vb vc vd cn0 cfv cc0 wceq c0p wne cdgr cle wbr ccoe cabs wral w3a
      cv crab cz cply wrex cc cmpt eqid aannenlem3 ) ABFCSDSGHIDESZJKUHLGBSZMNA
      SUHOGGPGUIMNAFQREUAUBGTUCCUDTUEZBCDEUJUFUG $.
      $( [16-Nov-2014] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    The Ackermann bijection
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c cdsum $.

  ${
    $d x y z w $.

    $( Extend class notation to include indexed cardinal sums. $)
    ccsum $a class cdsum $.

    $( Define indexed (k-ary) cardinal sums.  This is intended primarily to
       replace ` sum_ ` in subsystems without ~ ax-inf ; since ordinal addition
       is not commutative, finite sums of ordinals would be less useful, but
       cardinal sum is commutative and coincides with ordinal sum precisely
       where both are commutative. $)
    df-cdsum $a |- cdsum = { <. x , y >. | ( Fun x /\
        y = { <. z , w >. | w e. ( x ` z ) } ) } $.

    $d A u x y z w $.  $d B u x y z w $.

    $( Value of an indexed cardinal sum. $)
    cdsumval $p |- ( ( Fun A /\ A e. V ) -> ( cdsum ` A ) =
        { <. z , w >. | w e. ( A ` z ) } ) $=
      ( vu vx vy wcel wfun cvv ccsum cfv cv copab wceq elex wa cab funeq eqid
      elab4g biimpri ancoms fveq1 eleq2d opabbidv eleq1d cdm dmex abid2 eqeltri
      vex a1i opabex3 elfvdm ancri ssopab2i ssexi vtoclg adantl df-cdsum anbi1i
      fvex elab opabbii eqtr4i fvopab4g syl2anc sylan2 ) CDHCIZCJHZCKLBMZAMZCLZ
      HZABNZOZCDPVJVKQCEMZIZERZHZVPJHZVQVKVJWAWAVKVJQVSVJECVTVRCSVTTUAUBUCVKWBV
      JVLVMFMZLZHZABNZJHWBFCJWCCOZWFVPJWGWEVOABWGWDVNVLVMWCCUDUEUFZUGWFVMWCUHZH
      ZWEQZABNWEABWIWCFULZUIWEBRZJHWJWMWDJBWDUJVMWCVCUKUMUNWEWKABWEWJVLVMWCUOUP
      UQURUSUTFGCWFVPVTJKWHKWCIZGMWFOZQZFGNWCVTHZWOQZFGNFGABVAWRWPFGWQWNWOVSWNE
      WCWLVRWCSVDVBVEVFVGVHVI $.
      $( [19-Nov-2014] $)

    $d D y z u v $.  $d v u x $.

    $( Value of an indexed cardinal sum. $)
    cdsumval2 $p |- ( A e. Fin -> ( cdsum ` ( x e. A |-> D ) ) =
            { <. x , y >. | ( x e. A /\ y e. ( _I ` D ) ) } ) $=
      ( vz vu vv cfn wcel cfv cv copab cid wa cvv wceq csb syl ax-17 vex funmpt
      cmpt ccsum wfun a1i mptexg cdsumval syl2anc cdm elfvdm eqid dmmptss sseli
      pm4.71ri csbeq1 wel hbcsb1 csbeq1a cbvmpt fvmpti adantl pm5.32da opabbidv
      eleq2d syl5bb hbfv hban weq eleq1 fveq2d anbi12d cbvopab1 syl6eqr eqtrd )
      CHIZACDUBZUCJZBKZEKZVPJZIZEBLZAKZCIZVRDMJZIZNZABLZVOVPUDZVPOIZVQWBPWIVOAC
      DUAUEACDHUFZEBVPOUGUHVOWBVSCIZVRAVSDQZMJZIZNZEBLZWHVOWJWBWQPWKWJWAWPEBWAW
      LWANWJWPWAWLWAVSVPUIZIWLVRVSVPUJWRCVSACDVPVPUKULUMRUNWJWLWAWOWJWLNVTWNVRW
      LVTWNPWJFVSAFKZDQZWMCVPAWSVSDUOAFGCDWTGKDIFSAGWSDFTGFUPASUQAWSDURUSUTVAVD
      VBVEVCRWGWPABEWGESWLWOAWLASABWMMVRMIASABVSDETBEUPASUQVFVGAEVHZWDWLWFWOWCV
      SCVIXAWEWNVRXADWMMAVSDURVJVDVKVLVMVN $.
      $( [19-Nov-2014] $)

    $( Value of an indexed cardinal sum. $)
    cdsumval3 $p |- ( ( A e. Fin /\ A. x e. A D e. V ) ->
          ( cdsum ` ( x e. A |-> D ) ) =
            { <. x , y >. | ( x e. A /\ y e. D ) } ) $=
      ( cfn wcel wral cmpt ccsum cfv cv cid wa copab cdsumval2 wceq elex ralimi
      cvv hbra1 ax-17 wb ra4 fvi eleq2d syl6 pm5.32d opabbid syl sylan9eq ) CFG
      DEGZACHZACDIJKALCGZBLZDMKZGZNZABOZUNUODGZNZABOZABCDPUMDTGZACHZUSVBQULVCAC
      DERSVDURVAABVCACUAVDBUBVDUNUQUTVDUNVCUQUTUCVCACUDVCUPDUODTUEUFUGUHUIUJUK
      $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d A a b x $.  $d B a b x $.  $d D a $.
    $( Union of index sets of cardinal sum (non-cardinal property). $)
    cdsumun $p |- ( ( A u. B ) e. Fin -> ( cdsum `
          ( x e. ( A u. B ) |-> D ) ) = ( ( cdsum ` ( x e. A |-> D ) ) u.
          ( cdsum ` ( x e. B |-> D ) ) ) ) $=
      ( va cun cfn wcel cv cid cfv wa copab cmpt ccsum wo elun anbi1i cdsumval2
      wceq andir bitri opabbii unopab eqtr4i unfir uneq12 syl2an syl 3eqtr4a )
      BCFZGHZAIZUKHZEIDJKHZLZAEMZUMBHZUOLZAEMZUMCHZUOLZAEMZFZAUKDNOKABDNOKZACDN
      OKZFZUQUSVBPZAEMVDUPVHAEUPURVAPZUOLVHUNVIUOUMBCQRURVAUOUAUBUCUSVBAEUDUEAE
      UKDSULBGHZCGHZLVGVDTZBCUFVJVEUTTVFVCTVLVKAEBDSAECDSVEUTVFVCUGUHUIUJ $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d A a b c x $.  $d B a b c y $.  $d C a b c $.  $d D a b c $.

    $( Cardinal sum is a subset of a cross product. $)
    cdsumssxpfi $p |- ( A e. Fin -> ( cdsum ` ( x e. A |-> D ) ) C_
        ( A X. _V ) ) $=
      ( va cfn wcel cmpt ccsum cfv cv cid copab cvv cxp cdsumval2 wss simpl vex
      wa jctir ssopab2i df-xp sseqtr4i a1i eqsstrd ) BEFZABCGHIAJBFZDJZCKIFZSZA
      DLZBMNZADBCOUKULPUFUKUGUHMFZSZADLULUJUNADUJUGUMUGUIQDRTUAADBMUBUCUDUE $.
      $( [19-Nov-2014] $)

    $( Cardinal sums with disjoint index sets are disjoint (non-cardinal
       property). $)
    cdsumdisj $p |- ( ( A e. Fin /\ B e. Fin /\ ( A i^i B ) = (/) ) ->
        ( ( cdsum ` ( x e. A |-> C ) ) i^i
          ( cdsum ` ( y e. B |-> D ) ) ) = (/) ) $=
      ( cfn wcel cin wceq cmpt ccsum cfv cvv cxp wss cdsumssxpfi incom syl5eq
      c0 w3a 3ad2ant1 3ad2ant2 xpdisj1 3ad2ant3 ssdisj syl2anc ) CGHZDGHZCDITJZ
      UAZACEKLMZCNOZPZUMBDFKLMZIZTJULUOITJUHUIUNUJACEQUBUKUPUOUMIZTUMUORUKUODNO
      ZPZURUMIZTJZUQTJUIUHUSUJBDFQUCUJUHVAUIUJUTUMURITURUMRCDNNUDSUEUOURUMUFUGS
      ULUMUOUFUG $.
      $( [19-Nov-2014] $)

    $( Cardinal sum with an empty index set. $)
    cdsum0 $p |- ( cdsum ` ( x e. (/) |-> C ) ) = (/) $=
      ( cfn wcel cmpt ccsum cfv wss wceq 0fin cvv cxp cdsumssxpfi xp0r syl6sseq
      c0 ss0 mp2b ) PCDZAPBEFGZPHTPIJSTPKLPAPBMKNOTQR $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d A x y a b $.  $d ph x y a b $.  $d B x y a b $.  $d C x y a b $.
    $d D y a b $.
    cdsumsplitfi.a $e |- ( ph -> A e. Fin ) $.
    cdsumsplitfi.b $e |- ( ph -> ( B u. C ) = A ) $.
    cdsumsplitfi.c $e |- ( ph -> ( B i^i C ) = (/) ) $.
    $( Split a finite-indexed cardinal sum. $)
    cdsumsplitfi $p |- ( ph -> ( cdsum ` ( x e. A |-> D ) ) ~~
          ( ( cdsum ` ( x e. B |-> D ) ) +c
            ( cdsum ` ( x e. C |-> D ) ) ) ) $=
      ( cmpt ccsum cfv cen wbr cun wceq cfn wcel fvex syl co cin c0 wss eqeltrd
      ccda ssun1 ssfi sylancl ssun2 cdsumdisj syl3anc cdaun eqcomd mpteq1 eqtrd
      fveq2d cdsumun breqtrrd ensym ) ABDFJZKLZBEFJZKLZUFUAZBCFJZKLZMNVGVEMNAVE
      VBVDOZVGMAVBVDUBUCPZVEVHMNADQRZEQRZDEUBUCPVIADEOZQRZDVLUDVJAVLCQHGUEZDEUG
      VLDUHUIAVMEVLUDVKVNEDUJVLEUHUIIBBDEFFUKULVBVDVAKSVCKSUMTAVGBVLFJZKLZVHACV
      LPZVGVPPAVLCHUNVQVFVOKBCVLFUOUQTAVMVPVHPVNBDEFURTUPUSVEVGVFKSUTT $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d A x a b $.  $d B x a b $.
    $( Cross product is iterated cardinal sum. $)
    cdsumxpfi $p |- ( ( A e. Fin /\ B e. V ) -> ( cdsum ` ( x e. A |-> B ) ) =
        ( A X. B ) ) $=
      ( va cfn wcel wa cmpt ccsum cfv cv copab cxp cvv wral wceq elex ralrimivw
      syl cdsumval3 sylan2 df-xp syl6eqr ) BFGZCDGZHABCIJKZALBGELCGHAEMZBCNUFUE
      COGZABPZUGUHQUFUIUJCDRUIUIABCORSTAEBCOUAUBAEBCUCUD $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d A x a b $.  $d D a b $.

    $( Cardinal sum at a single point. $)
    cdsumsn $p |- ( A e. V -> ( cdsum ` ( x e. { A } |-> D ) ) ~~
          [_ A / x ]_ D ) $=
      ( va vb wcel csn cmpt ccsum cfv csb cen cv ax-17 cvv wbr cxp mpan adantl
      vex wel hbcsb1 csbeq1a cbvmpt elsni csbeq1d mpteq2ia eqtri fveq2i wa wceq
      cfn snfi cdsumxpfi snex xpcomeng xpsneng ancoms entr syl2anc eqbrtrd fvex
      wn enref brprc mpbiri pm2.61dan syl5eqbr ) BDGZABHZCIZJKEVKABCLZIZJKZVMMV
      LVNJVLEVKAENZCLZIVNAEFVKCVQFNCGEOAFVPCEUAFEUBAOUCAVPCUDUEEVKVQVMVPVKGAVPB
      CVPBUFUGUHUIUJVJVMPGZVOVMMQZVJVRUKZVOVKVMRZVMMVRVOWAULZVJVKUMGVRWBBUNEVKV
      MPUOSTVTWAVMVKRZMQZWCVMMQZWAVMMQVRWDVJVKPGVRWDBUPVKVMPPUQSTVRVJWEVMBPDURU
      SWAWCVMUTVAVBVRVDZVSVJWFVSVOVOMQVOVNJVCVEVOVMMVFVGTVHVI $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d ph x a b c $.  $d A a b c x $.  $d D a b c $.
    cdsumfi.a $e |- ( ph -> A e. Fin ) $.
    cdsumfi.b $e |- ( ( ph /\ x e. A ) -> D e. Fin ) $.
    $( Finiteness of cardinal sum. $)
    cdsumfi $p |- ( ph -> ( cdsum ` ( x e. A |-> D ) ) e. Fin ) $=
      ( va vc wss cmpt ccsum cfv cfn wcel wa wi c0 anbi2d eleq1d imbi12d adantr
      vb ssid cv csn cun wceq sseq1 mpteq1 fveq2d weq cdsum0 0fin eqeltri ssun1
      a1i sstr mpan anim2i imim1i w3a snfi mpan2 3ad2ant1 cdsumun syl simp3 csb
      unfi ssun2 vex snss sylibr ax-17 wel hbcsb1 hbel hbim eleq1 csbeq1a chvar
      sylan2 cen wbr wb cdsumsn ax-mp enfi syl2anc mpbird 3ad2ant2 eqeltrd 3exp
      cvv a2d syl5 findcard2 mpcom ) ACCIZBCDJZKLZMNZCUCCMNZAWSOZXBAXCWSEUAAGUD
      ZCIZOZBXEDJZKLZMNZPAQCIZOZBQDJZKLZMNZPAUBUDZCIZOZBXPDJZKLZMNZPZAXPHUDZUEZ
      UFZCIZOZBYEDJZKLZMNZPZXDXBPGUBHCXEQUGZXGXLXJXOYLXFXKAXEQCUHRYLXIXNMYLXHXM
      KBXEQDUIUJSTGUBUKZXGXRXJYAYMXFXQAXEXPCUHRYMXIXTMYMXHXSKBXEXPDUIUJSTXEYEUG
      ZXGYGXJYJYNXFYFAXEYECUHRYNXIYIMYNXHYHKBXEYEDUIUJSTXECUGZXGXDXJXBYOXFWSAXE
      CCUHRYOXIXAMYOXHWTKBXECDUIUJSTXOXLXNQMBDULUMUNUPYBYGYAPXPMNZYKYGXRYAYFXQA
      XPYEIYFXQXPYDUOXPYECUQURUSUTYPYGYAYJYPYGYAYJYPYGYAVAZYIXTBYDDJKLZUFZMYQYE
      MNZYIYSUGYPYGYTYAYPYDMNYTYCVBXPYDVIVCVDBXPYDDVEVFYQYAYRMNZYSMNYPYGYAVGYGY
      PUUAYAYGUUABYCDVHZMNZYFAYCCNZUUCYFYDCIZUUDYDYEIYFUUEYDXPVJYDYECUQURYCCHVK
      ZVLVMABUDZCNZOZDMNZPAUUDOZUUCPBHUUKUUCBUUKBVNBGGUUBMBGYCDUUFGHVOBVNVPXEMN
      BVNVQVRBHUKZUUIUUKUUJUUCUULUUHUUDAUUGYCCVSRUULDUUBMBYCDVTSTFWAWBZYGUUCYRU
      UBWCWDZUUAUUCWEUUMUUNYGYCWNNUUNUUFBYCDWNWFWGUPYRUUBMWHWIWJWKXTYRVIWIWLWMW
      OWPWQWRVC $.
      $( [19-Nov-2014] $)
  $}

  ${
    $d F a b c x y $.  $d G a b c x y $.  $d H a b c x y $.  $d A a b c x y $.
    $d B a b c x y $.

    $( A one-to-one mapping induces a one-to-one mapping on power sets. $)
    f1opw $p |- ( F : A -1-1-onto-> B -> ( b e. ~P A |-> ( F " b ) ) :
          ~P A -1-1-onto-> ~P B ) $=
      ( va cpw cv cima wcel wss crn imassrn wceq syl5sseq wfun cvv vex funimaex
      wb adantr wf1o ccnv cmpt eqid wfo f1ofo forn syl f1ofun elpwg 3syl mpbird
      dfdm4 f1odm syl5eqr dff1o3 simprbi wa elpwi adantl foimacnv syl2an eqcomd
      cdm imaeq2 eqeq2d syl5ibrcom wf1 f1of1 f1imacnv impbid f1o2d ) ABCUAZDEAF
      ZBFZCDGZHZCUBZEGZHZDVNVQUCZWAUDVMVQVOIZVPVNIZVMWBVQBJZVMCKZVQBCVPLVMABCUE
      ZWEBMABCUFZABCUGUHNVMCOVQPIWBWDSABCUICVPDQRVQBPUJUKULTVMVTVNIZVSVOIZVMWHV
      TAJZVMVRKZVTAVRVSLVMWKCVDACUMABCUNUONVMVROZVTPIWHWJSVMWFWLABCUPUQVRVSEQRV
      TAPUJUKULTVMWCWIURZURZVPVTMZVSVQMZWNWPWOVSCVTHZMWNWQVSVMWFVSBJZWQVSMWMWGW
      IWRWCVSBUSUTABVSCVAVBVCWOVQWQVSVPVTCVEVFVGWNWOWPVPVRVQHZMWNWSVPVMABCVHVPA
      JZWSVPMWMABCVIWCWTWIVPAUSTABVPCVJVBVCWPVTWSVPVSVQVRVEVFVGVKVL $.
      $( [18-Nov-2014] $)

    $( An ordinal number is a proper subset of its successor. $)
    onpsssuc $p |- ( A e. On -> A C. suc A ) $=
      ( con0 wcel csuc wpss sucidg wb eloni ordsuc sylib ordelpss syl2anc mpbid
      word ) ABCZAADZCZAPEZABFOANZPNZQRGAHZOSTUAAIJAPKLM $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij2lem1 $p |- ( A e. om -> ~P A C_ ( ~P om i^i Fin ) ) $=
      ( va com wcel cpw cfn cin cv wa wss word ordom ordelss sspwb sylib sselda
      mpan con0 onfin2 inss2 eqsstri sseli elpwi ssfi syl2an sylanbrc ex ssrdv
      elin ) ACDZBAEZCEZFGZUJBHZUKDZUNUMDZUJUOIUNULDUNFDZUPUJUKULUNUJACJZUKULJC
      KUJURLCAMQACNOPUJAFDUNAJUQUOCFACRFGFSRFTUAUBUNAUCAUNUDUEUNULFUIUFUGUH $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem1 $p |- ( -. A e. B -> ( B i^i suc A ) = ( B i^i A ) ) $=
      ( wcel wn csuc cin csn cun df-suc ineq2i indi eqtri c0 wceq disjsn uneq2d
      biimpri un0 syl6eq syl5eq ) ABCDZBAEZFZBAFZBAGZFZHZUDUCBAUEHZFUGUBUHBAIJB
      AUEKLUAUGUDMHUDUAUFMUDUFMNUABAOQPUDRST $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem2 $p |- ( A e. B -> ( B i^i suc A ) =
        ( { A } u. ( B i^i A ) ) ) $=
      ( wcel csuc cin csn cun df-suc ineq2i indi uncom 3eqtri wss snssi sseqin2
      wceq sylib uneq1d syl5eq ) ABCZBADZEZBAFZEZBAEZGZUCUEGUBBAUCGZEUEUDGUFUAU
      GBAHIBAUCJUEUDKLTUDUCUETUCBMUDUCPABNUCBOQRS $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem3 $p |- ( A e. om -> A e. ( ~P om i^i Fin ) ) $=
      ( com wcel cpw cfn cin wss word ordom mpan elpwg mpbird con0 onfin2 inss2
      ordelss eqsstri sseli elin sylanbrc ) ABCZABDZCZAECAUBEFCUAUCABGZBHUAUDIB
      APJABBKLBEABMEFENMEOQRAUBEST $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem4 $p |- ( A e. om -> { A } e. ( ~P om i^i Fin ) ) $=
      ( com wcel csn cpw cfn cin snelpwi snfi a1i elin sylanbrc ) ABCZADZBEZCNF
      CZNOFGCABHPMAIJNOFKL $.
      $( [19-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem5 $p |- ( A e. om -> ( card ` ~P suc A ) =
        ( ( card ` ~P A ) +o ( card ` ~P A ) ) ) $=
      ( va cpw ccrd cfv coa co wceq com wcel ccda cen wbr ovex c2o cxp cmap cfn
      entr syl csuc suceq pweqd fveq2d pweq oveq12d eqeq12d cvv vex sucex pw2en
      cv csn cun df-suc oveq2i word cin c0 nnord orddisj snex 2onn mapunen 3syl
      elexi enref mapsnen xpen sylancl syl5eqbr xpex ensymi sylancr pwex xp2cda
      mp2an syl6breq con0 onfin2 inss2 eqsstri sseli pwfi ficardid fvex syl2anc
      sylib cdaen ensym carden2b mpsyl ficardom nnacda eqtrd vtoclga ) BULZUAZC
      ZDEZWQCZDEZXBFGZHAUAZCZDEZACZDEZXHFGZHBAIWQAHZWTXFXCXIXJWSXEDXJWRXDWQAUBU
      CUDXJXBXHXBXHFXJXAXGDWQAUEUDZXKUFUGWQIJZWTXBXBKGZDEZXCXMUHJXLWSXMLMZWTXNH
      XBXBKNXLWSXAXAKGZLMXPXMLMZXOXLWSXAOPZXPLXLWSOWRQGZLMXSXRLMZWSXRLMWRWQBUIZ
      UJUKXLXSOWQQGZOPZLMYCXRLMXTXLXSOWQWQUMZUNZQGZYCLWRYEOQWQUOUPXLYFYBOYDQGZP
      ZLMZYHYCLMZYFYCLMXLWQUQWQYDURUSHYIWQUTWQVAWQYDOYAWQVBOIVCVFZVDVEYBYBLMYGO
      LMYJYBOWQQNZVGOWQYAVHYBYBYGOYLYKVIVQYFYHYCSVJVKXRYCYBOYLYKVLXAYBLMOOLMXRY
      CLMWQYAUKOYKVGXAYBOOYLYKVIVQVMXSYCXRSVJWSXSXRSVNXAWQYAVOZVPVRXLXMXPLMZXQX
      LXBXALMZYOYNXLXARJZYOXLWQRJYPIRWQIVSRURRVTVSRWAWBWCWQWDWHZXAWETZYRXBXAXBX
      AXADWFZYMYSYMWIWGXMXPXAXAKNWJTWSXPXMSWGWSXMUHWKWLXLXBIJZYTXNXCHXLYPYTYQXA
      WMTZUUAXBXBWNWGWOWP $.
      $( [19-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij1lem6 $p |- ( ( A e. ( ~P om i^i Fin ) /\
          B e. ( ~P om i^i Fin ) ) ->
        ( A u. B ) e. ( ~P om i^i Fin ) ) $=
      ( com cpw cfn cin wcel cun wss inss1 sseli elpwi simpl simpr unssd syl2an
      wa wb inss2 unfi elpwg syl mpbird elin sylanbrc ) ACDZEFZGZBUGGZQZABHZUFG
      ZUKEGZUKUGGUJULUKCIZUHAUFGZBUFGZUNUIUGUFAUFEJZKUGUFBUQKUOACIZBCIZUNUPACLB
      CLURUSQABCURUSMURUSNOPPUJUMULUNRUHAEGBEGUMUIUGEAUFESZKUGEBUTKABTPZUKCEUAU
      BUCVAUKUFEUDUE $.
      $( [18-Nov-2014] $)

    ackbij.f $e |- F = ( x e. ( ~P om i^i Fin ) |->
        ( card ` ( cdsum ` ( y e. x |-> ~P y ) ) ) ) $.
    $( Lemma for ~ ackbij1 . $)
    ackbij1lem7 $p |- ( A e. ( ~P om i^i Fin ) -> ( F ` A ) =
        ( card ` ( cdsum ` ( y e. A |-> ~P y ) ) ) ) $=
      ( cv cpw cmpt ccsum cfv ccrd com cfn cin wceq mpteq1 fveq2d fvex fvmpt )
      ACBAFZBFGZHZIJZKJBCUAHZIJZKJLGMNDTCOZUCUEKUFUBUDIBTCUAPQQEUEKRS $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem8 $p |- ( A e. om -> ( F ` { A } ) = ( card ` ~P A ) ) $=
      ( va com wcel csn cfv cv cpw cmpt ccsum ccrd cfn cin wceq cvv cen syl wbr
      ackbij1lem4 ackbij1lem7 pwexg csb cdsumsn a17d pweq csbiegf carden2b sylc
      breqtrd eqtrd ) CGHZCIZDJZBUPBKZLZMNJZOJZCLZOJZUOUPGLPQHUQVARCUCABUPDEUDU
      AUOVBSHUTVBTUBVAVCRCGUEUOUTBCUSUFVBTBCUSGUGBFCUSVBGUOFKVBHBUHURCUIUJUMUTV
      BSUKULUN $.
      $( [19-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem9 $p |- ( ( A e. ( ~P om i^i Fin ) /\ B e. ( ~P om i^i Fin ) /\
          ( A i^i B ) = (/) ) ->
        ( F ` ( A u. B ) ) = ( ( F ` A ) +o ( F ` B ) ) ) $=
      ( com cfn cin wcel wceq ccsum cfv ccrd co cen wbr sseli syl fvex cpw cmpt
      c0 w3a cun coa ccda cvv ovex inss2 ackbij1lem6 3adant3 sseldi eqidd simp3
      cv cdsumsplitfi 3ad2ant1 wa inss1 elpwi con0 onfin2 eqsstri syl6ss sselda
      wss pwfi sylib cdsumfi ficardid ensym 3syl 3ad2ant2 syl2anc entr carden2b
      cdaen mpsyl ficardom nnacda eqtrd ackbij1lem7 oveqan12d 3eqtr4d ) CGUAZHI
      ZJZDWGJZCDIUCKZUDZBCDUEZBUPZUAZUBLMZNMZBCWNUBZLMZNMZBDWNUBZLMZNMZUFOZWLEM
      ZCEMZDEMZUFOZWKWPWSXBUGOZNMZXCXHUHJWKWOXHPQZWPXIKWSXBUGUIWKWOWRXAUGOZPQXK
      XHPQZXJWKBWLCDWNWKWGHWLWFHUJZWHWIWLWGJZWJCDUKULZUMWKWLUNWHWIWJUOUQWKWRWSP
      QZXAXBPQZXLWKWRHJZWSWRPQXPWKBCWNWHWICHJWJWGHCXMRURWKWMCJUSWMHJZWNHJZWKCHW
      MWKCGHWKCWFJZCGVGWHWIYAWJWGWFCWFHUTZRURCGVASGVBHIHVCVBHUJVDZVEVFWMVHZVIVJ
      ZWRVKWSWRWQLTZVLVMWKXAHJZXBXAPQXQWKBDWNWIWHDHJWJWGHDXMRVNWKWMDJUSXSXTWKDH
      WMWKDGHWKDWFJZDGVGWIWHYHWJWGWFDYBRVNDGVASYCVEVFYDVIVJZXAVKXBXAWTLTZVLVMWR
      WSXAXBYFWRNTYJXANTVRVOWOXKXHVPVOWOXHUHVQVSWKWSGJZXBGJZXIXCKWKXRYKYEWRVTSW
      KYGYLYIXAVTSWSXBWAVOWBWKXNXDWPKXOABWLEFWCSWHWIXGXCKWJWHWIXEWSXFXBUFABCEFW
      CABDEFWCWDULWE $.
      $( [19-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem10 $p |- F : ( ~P om i^i Fin ) --> om $=
      ( com cpw cfn cin wf wtru cmpt ccsum cfv ccrd wcel inss2 sseli con0 sylib
      cv wel wa onfin2 eqsstri wss vex elpw sselda sseldi pwfi cdsumfi ficardom
      inss1 syl adantl fmptd trud ) EFZGHZECIJAUSBATZBTZFZKLMZNMZECUTUSOZVDEOZJ
      VEVCGOVFVEBUTVBUSGUTURGPQVEBAUAUBZVAGOVBGOVGEGVAERGHGUCRGPUDVEUTEVAVEUTUR
      OUTEUEUSURUTURGUMQUTEAUFUGSUHUIVAUJSUKVCULUNUODUPUQ $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem11 $p |- ( ( A e. ( ~P om i^i Fin ) /\ B C_ A ) ->
        B e. ( ~P om i^i Fin ) ) $=
      ( com cpw cfn cin wcel wss wa inss1 sseli elpwi syl sstr sylan2 cvv ssexg
      wb elpwg mpbird ancoms inss2 ssfi sylan elin sylanbrc ) CGHZIJZKZDCLZMDUK
      KZDIKZDULKUNUMUOUNUMMZUODGLZUMUNCGLZURUMCUKKUSULUKCUKINOCGPQDCGRSUQDTKUOU
      RUBDCULUADGTUCQUDUEUMCIKUNUPULICUKIUFOCDUGUHDUKIUIUJ $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem12 $p |- ( ( B e. ( ~P om i^i Fin ) /\ A C_ B ) ->
        ( F ` A ) C_ ( F ` B ) ) $=
      ( com cpw cfn cin wcel wss cfv cdif ackbij1lem11 ffvelrn sylancr a1i wceq
      wa coa co wf ackbij1lem10 syldan nnaword1 syl2anc cun disjdif ackbij1lem9
      difss c0 syl3anc undif biimpi adantl fveq2d eqtr3d sseqtrd ) DGHIJZKZCDLZ
      TZCEMZVDDCNZEMZUAUBZDEMZVCVDGKZVFGKZVDVGLVCUTGEUCZCUTKZVIABEFUDZABDCEFOZU
      TGCEPQVCVKVEUTKZVJVMVAVBVEDLZVOVPVCDCUKRABDVEEFOUEZUTGVEEPQVDVFUFUGVCCVEU
      HZEMZVGVHVCVLVOCVEJULSZVSVGSVNVQVTVCCDUIRABCVEEFUJUMVCVRDEVBVRDSZVAVBWACD
      UNUOUPUQURUS $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem13 $p |- ( F ` (/) ) = (/) $=
      ( c0 cfv coa co wceq cun com wcel cpw cfn ackbij1lem10 peano1 f0cli ax-mp
      cin mp3an nna0 un0 fveq2i ackbij1lem3 ackbij1lem9 3eqtr2ri wb nnacan mpbi
      in0 ) ECFZUKGHZUKEGHZIZUKEIZUMUKEEJZCFZULUKKLZUMUKIKMNSZKECABCDOPQZUKUARU
      PECEUBUCEUSLZVAEESEIUQULIEKLZVAPEUDRZVCEUJABEECDUETUFURURVBUNUOUGUTUTPUKU
      KEUHTUI $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem14 $p |- ( A e. om -> ( F ` { A } ) = suc ( F ` A ) ) $=
      ( com wcel cfv cpw ccrd csuc wceq c0 pweq fveq2d suceq syl coa adantr cfn
      va vb csn ackbij1lem8 cv fveq2 eqeq12d weq c1o df-1o pw0 fveq2i cvv ax-mp
      0ex cardsn eqtri ackbij1lem13 3eqtr4i wa co adantl ackbij1lem5 cun df-suc
      oveq2 equncomi cin ackbij1lem4 ackbij1lem3 incom word orddisj ackbij1lem9
      nnord syl5eq syl3anc oveq1d eqtrd con0 onfin2 inss2 eqsstri pwfi ficardom
      sseli sylib ackbij1lem10 ffvelrni nnasuc syl2anc eqtr4d 3eqtr4d ex finds
      ) CFGCUCDHCIZJHZCDHZKZABCDEUDUAUEZIZJHZWTDHZKZLMIZJHZMDHZKZLUBUEZIZJHZXID
      HZKZLZXIKZIZJHZXODHZKZLZWQWSLUAUBCWTMLZXBXFXDXHYAXAXEJWTMNOYAXCXGLXDXHLWT
      MDUFXCXGPQUGUAUBUHZXBXKXDXMYBXAXJJWTXINOYBXCXLLXDXMLWTXIDUFXCXLPQUGWTXOLZ
      XBXQXDXSYCXAXPJWTXONOYCXCXRLXDXSLWTXODUFXCXRPQUGWTCLZXBWQXDWSYDXAWPJWTCNO
      YDXCWRLXDWSLWTCDUFXCWRPQUGUIMKZXFXHUJXFMUCZJHZUIXEYFJUKULMUMGYGUILUOMUMUP
      UNUQXGMLXHYELABDEURXGMPUNUSXIFGZXNXTYHXNUTZXKXKRVAZXKXMRVAZXQXSXNYJYKLYHX
      KXMXKRVFVBYHXQYJLXNXIVCSYIXSXKXLRVAZKZYKYIXRYLLXSYMLYIXRXIUCZXIVDZDHZYLXO
      YODXOXIYNXIVEVGULYIYPYNDHZXLRVAZYLYIYNFITVHZGZXIYSGZYNXIVHZMLZYPYRLYHYTXN
      XIVISYHUUAXNXIVJSZYHUUCXNYHUUBXIYNVHZMYNXIVKYHXIVLUUEMLXIVOXIVMQVPSABYNXI
      DEVNVQYIYQXKXLRYHYQXKLXNABXIDEUDSVRVSVPXRYLPQYIXKFGZXLFGZYKYMLYIXJTGZUUFY
      HUUHXNYHXITGUUHFTXIFVTTVHTWAVTTWBWCWFXIWDWGSXJWEQYIUUAUUGUUDYSFXIDABDEWHW
      IQXKXLWJWKWLWMWNWOVS $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem15 $p |- ( ( ( A e. ( ~P om i^i Fin ) /\
          B e. ( ~P om i^i Fin ) ) /\ ( c e. om /\ c e. A /\ -. c e. B ) ) ->
        -. ( F ` ( A i^i suc c ) ) = ( F ` ( B i^i suc c ) ) ) $=
      ( com cfn cin wcel wa wn cfv wceq wpss wss con0 syl syl2anc cpw cv simpr1
      w3a csuc wne word ordom ordelss mpan vex elpw sylibr onfin2 inss2 eqsstri
      sseli elin sylanbrc ackbij1lem1 a1i eqsstrd ackbij1lem12 csn ackbij1lem10
      simpr3 ffvelrni nnon 3syl ackbij1lem14 psseq2d mpbird simpll ackbij1lem11
      onpsssuc inss1 ssun1 simpr2 ackbij1lem2 syl5sseqr psssstr sspsstr simprbi
      cun df-pss necomd df-ne sylib ) CHUAZIJZKZDWJKZLZFUBZHKZWNCKZWNDKMZUDZLZC
      WNUEZJZENZDWTJZENZUFXBXDOMWSXDXBWSXDXBPZXDXBUFZWSXDWNENZQZXGXBPZXEWSWNWJK
      ZXCWNQXHWSWOXJWMWOWPWQUCZWOWNWIKZWNIKXJWOWNHQZXLHUGWOXMUHHWNUIUJWNHFUKULU
      MHIWNHRIJIUNRIUOUPUQWNWIIURUSSZWSXCDWNJZWNWSWQXCXOOWMWOWPWQVFWNDUTSXOWNQW
      SDWNUOVAVBABXCWNEGVCTWSXGWNVDZENZPZXQXBQZXIWSXRXGXGUEZPZWSXGRKZYAWSXJXGHK
      YBXNWJHWNEABEGVEVGXGVHVIXGVOSWSXQXTXGWSWOXQXTOXKABWNEGVJSVKVLWSXAWJKZXPXA
      QXSWSWKXACQZYCWKWLWRVMYDWSCWTVPVAABCXAEGVNTWSXPCWNJZWDZXPXAXPYEVQWSWPXAYF
      OWMWOWPWQVRWNCVSSVTABXPXAEGVCTXGXQXBWATXDXGXBWBTXEXDXBQXFXDXBWEWCSWFXBXDW
      GWH $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem16 $p |- ( ( A e. ( ~P om i^i Fin ) /\ B e. ( ~P om i^i Fin ) )
        ->
        ( ( F ` A ) = ( F ` B ) -> A = B ) ) $=
      ( com cfn cin wcel cfv wceq wi wss syl c0 ineq2 fveq2d eqeq12d w3a va cpw
      vb cun cuni csuc inss1 sseli elpwi adantr adantl unssd inss2 unfi nnunifi
      wa syl2an syl2anc peano2 cv imbi12d imbi2d weq in0 eqtr4i a1i12 co simp13
      csn coa 3simpa ackbij1lem2 3ad2ant2 ackbij1lem4 simprl ackbij1lem11 incom
      sylancl word nnord orddisj ssdisj sylancr syl5eq syl3anc 3ad2ant1 syl3an1
      ackbij1lem9 eqtrd 3ad2ant3 simprr 3eqtr3d wb ackbij1lem10 ffvelrni nnacan
      3adant3 mpbid uneq2 ad2antrr ad2antlr 3eqtr4d 3adant1 embantd 3exp eqcomd
      ex wn simp12r simp12l simp11 simp3 simp2 syl23anc pm2.65i pm2.21i pm2.61d
      ackbij1lem15 ackbij1lem1 biimpd mpd biimprd com34 finds mpcom con0 omsson
      a2d ssun1 syl6ss onsucuni syl5ss df-ss sylib ssun2 ) CGUBZHIZJZDYQJZUPZCC
      DUDZUEZUFZIZEKZDUUCIZEKZLZUUDUUFLZMZCEKZDEKZLZCDLZMUUCGJZYTUUJYTUUBGJZUUO
      YTUUAGNUUAHJZUUPYTCDGYRCGNZYSYRCYPJUURYQYPCYPHUGZUHCGUIOUJYSDGNZYRYSDYPJU
      UTYQYPDUUSUHDGUIOUKULZYRCHJDHJUUQYSYQHCYPHUMZUHYQHDUVBUHCDUNUQUUAUOURUUBU
      SOYTCUAUTZIZEKZDUVCIZEKZLZUVDUVFLZMZMYTCPIZEKZDPIZEKZLZUVKUVMLZMZMYTCUCUT
      ZIZEKZDUVRIZEKZLZUVSUWALZMZMYTCUVRUFZIZEKZDUWFIZEKZLZUWGUWILZMZMYTUUJMUAU
      CUUCUVCPLZUVJUVQYTUWNUVHUVOUVIUVPUWNUVEUVLUVGUVNUWNUVDUVKEUVCPCQZRUWNUVFU
      VMEUVCPDQZRSUWNUVDUVKUVFUVMUWOUWPSVAVBUAUCVCZUVJUWEYTUWQUVHUWCUVIUWDUWQUV
      EUVTUVGUWBUWQUVDUVSEUVCUVRCQZRUWQUVFUWAEUVCUVRDQZRSUWQUVDUVSUVFUWAUWRUWSS
      VAVBUVCUWFLZUVJUWMYTUWTUVHUWKUVIUWLUWTUVEUWHUVGUWJUWTUVDUWGEUVCUWFCQZRUWT
      UVFUWIEUVCUWFDQZRSUWTUVDUWGUVFUWIUXAUXBSVAVBUVCUUCLZUVJUUJYTUXCUVHUUHUVIU
      UIUXCUVEUUEUVGUUGUXCUVDUUDEUVCUUCCQZRUXCUVFUUFEUVCUUCDQZRSUXCUVDUUDUVFUUF
      UXDUXESVAVBYTUVOUVPUVKPUVMCVDDVDVEVFUVRGJZYTUWEUWMUXFYTUWKUWEUWLUXFYTUWKU
      WEUWLMZUXFYTUWKTZUVRDJZUXGUXHUVRCJZUXIUXGMUXHUXJUXIUXGUXHUXJUXITZUWCUWDUW
      LUXKUVRVIZEKZUVTVJVGZUXMUWBVJVGZLZUWCUXKUWHUWJUXNUXOUXFYTUWKUXJUXIVHUXHUX
      FYTUPZUXJUXIUWHUXNLUXFYTUWKVKZUXQUXJUXITZUWHUXLUVSUDZEKZUXNUXJUXQUWHUYALU
      XIUXJUWGUXTEUVRCVLZRVMUXQUXJUYAUXNLZUXIUXQUXLYQJZUVSYQJZUXLUVSIZPLUYCUXFU
      YDYTUVRVNUJZUXQYRUVSCNUYEUXFYRYSVOCUVRUGABCUVSEFVPVRZUXQUYFUVSUXLIZPUXLUV
      SVQUXQUVSUVRNUVRUXLIPLZUYIPLCUVRUMUXFUYJYTUXFUVRVSUYJUVRVTUVRWAOUJZUVSUVR
      UXLWBWCWDABUXLUVSEFWHWEWFWIWGUXHUXQUXJUXIUWJUXOLUXRUXSUWJUXLUWAUDZEKZUXOU
      XIUXQUWJUYMLUXJUXIUWIUYLEUVRDVLZRWJUXQUXJUYMUXOLZUXIUXQUYDUWAYQJZUXLUWAIZ
      PLUYOUYGUXQYSUWADNUYPUXFYRYSWKDUVRUGABDUWAEFVPVRZUXQUYQUWAUXLIZPUXLUWAVQU
      XQUWAUVRNUYJUYSPLDUVRUMUYKUWAUVRUXLWBWCWDABUXLUWAEFWHWEWFWIWGWLUXHUXJUXPU
      WCWMZUXIUXFYTUYTUWKUXQUXMGJZUVTGJZUWBGJZUYTUXQUYDVUAUYGYQGUXLEABEFWNZWOOU
      XQUYEVUBUYHYQGUVSEVUDWOOUXQUYPVUCUYRYQGUWAEVUDWOOUXMUVTUWBWPWEWQWFWRUXJUX
      IUWDUWLMZUXHUXJUXIUPZUWDUWLVUFUWDUPUXTUYLUWGUWIUWDUXTUYLLVUFUVSUWAUXLWSUK
      UXJUWGUXTLUXIUWDUYBWTUXIUWIUYLLUXJUWDUYNXAXBXGXCXDXEUXHUXJXHZUXIUXGUXHVUG
      UXITZUXGVUHUWJUWHLZVUHUWHUWJUXFYTUWKVUGUXIVHXFVUHYSYRUXFUXIVUGVUIXHYRYSUX
      FUWKVUGUXIXIYRYSUXFUWKVUGUXIXJUXFYTUWKVUGUXIXKUXHVUGUXIXLUXHVUGUXIXMABDCE
      UCFXRXNXOXPXEXQUXHUXJUXIXHZUXGMUXHUXJVUJUXGUXHUXJVUJTZUXGVUKUWKUXFYTUWKUX
      JVUJVHVUKYRYSUXFUXJVUJUWKXHYRYSUXFUWKUXJVUJXJYRYSUXFUWKUXJVUJXIUXFYTUWKUX
      JVUJXKUXHUXJVUJXMUXHUXJVUJXLABCDEUCFXRXNXOXPXEUXHVUGVUJUXGUXHVUGVUJTZUWCU
      WDUWLVULUWKUWCUXFYTUWKVUGVUJVHVUGVUJUWKUWCMUXHVUGVUJUPZUWKUWCVUMUWHUVTUWJ
      UWBVUMUWGUVSEVUGUWGUVSLVUJUVRCXSUJZRVUMUWIUWAEVUJUWIUWALVUGUVRDXSUKZRSXTX
      CYAVUGVUJVUEUXHVUMUWLUWDVUMUWGUVSUWIUWAVUNVUOSYBXCXDXEXQXQXEYCYHYDYEYTUUH
      UUMUUIUUNYTUUEUUKUUGUULYTUUDCEYTCUUCNUUDCLYTCUUAUUCCDYIYTUUAYFNUUAUUCNYTU
      UAGYFUVAYGYJUUAYKOZYLCUUCYMYNZRYTUUFDEYTDUUCNUUFDLYTDUUAUUCDCYOVUPYLDUUCY
      MYNZRSYTUUDCUUFDVUQVURSVAWR $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem17 $p |- F : ( ~P om i^i Fin ) -1-1-> om $=
      ( va vb com cpw cfn cin wf1 wf cv cfv wceq weq wi wral dff13 ackbij1lem10
      ackbij1lem16 rgen2a mpbir2an ) GHIJZGCKUDGCLEMZCNFMZCNOEFPQZFUDREUDREFUDG
      CSABCDTUGEFUDABUEUFCDUAUBUC $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij1 . $)
    ackbij1lem18 $p |- ( A e. ( ~P om i^i Fin ) -> E. b e. ( ~P om i^i Fin )
          ( F ` b ) = suc ( F ` A ) ) $=
      ( com cfn cin wcel cun cfv csuc wceq wss c0 wn sylancr syl coa va cpw csn
      cdif cint wrex difss ackbij1lem11 mpan2 con0 wne omsson sstri ominf inss2
      cv sseli difinf 0fin eleq1 mpbiri necon3bi sseldi ackbij1lem4 ackbij1lem6
      onint syl2anc eldifn disjsn sylibr ssdisj ackbij1lem9 ackbij1lem14 oveq2d
      co syl3anc ackbij1lem10 ffvelrni ackbij1lem3 nnasuc incom eqtri a1i uncom
      disjdif wa wo onnmin mpan con2i adantl word ordom ordelss sselda simplbi2
      eldif orrd orcomd orel1 sylc ssrdv undif sylib syl5eq fveq2d eqtr3d suceq
      ex eqtrd 3eqtrd fveq2 eqeq1d rcla4ev ) CGUBZHIZJZCGCUDZUEZUDZXSUCZKZXPJZY
      BDLZCDLZMZNZEUPZDLZYFNZEXPUFXQXTXPJZYAXPJZYCXQXTCOZYKCXSUGZABCXTDFUHUIZXQ
      XSGJZYLXQXRGXSGCUGZXQXRUJOZXRPUKZXSXRJZXRGUJYQULUMZXQXRHJZQZYSXQGHJQCHJUU
      CUNXPHCXOHUOUQGCURRUUBXRPXRPNUUBPHJUSXRPHUTVAVBSXRVFRZVCZXSVDSZXTYAVEVGXQ
      YDXTDLZYADLZTVOZUUGXSDLZMZTVOZYFXQYKYLXTYAIPNZYDUUINYOUUFXQYMCYAIPNZUUMYN
      XQXSCJQZUUNXQYTUUOUUDXSGCVHSCXSVIVJXTCYAVKRABXTYADFVLVPXQUUHUUKUUGTXQYPUU
      HUUKNUUEABXSDFVMSVNXQUULUUGUUJTVOZMZYFXQUUGGJZUUJGJZUULUUQNXQYKUURYOXPGXT
      DABDFVQZVRSXQXSXPJZUUSXQYPUVAUUEXSVSSZXPGXSDUUTVRSUUGUUJVTVGXQUUPYENUUQYF
      NXQXTXSKZDLZUUPYEXQYKUVAXTXSIZPNZUVDUUPNYOUVBUVFXQUVEXSXTIPXTXSWAXSCWEWBW
      CABXTXSDFVLVPXQUVCCDXQUVCXSXTKZCXTXSWDXQXSCOUVGCNXQUAXSCXQUAUPZXSJZUVHCJZ
      XQUVIWFZUVHXRJZQZUVLUVJWGZUVJUVIUVMXQUVLUVIYRUVLUVIQUUAXRUVHWHWIWJWKUVKUV
      HGJZUVNXQXSGUVHXQGWLYPXSGOWMUUEGXSWNRWOUVOUVJUVLUVOUVJUVLUVLUVOUVJQUVHGCW
      QWPWRWSSUVLUVJWTXAXIXBXSCXCXDXEXFXGUUPYEXHSXJXKYJYGEYBXPYHYBNYIYDYFYHYBDX
      LXMXNVG $.
      $( [18-Nov-2014] $)

    $( The Ackermann bijection, part 1: each natural number can be uniquely
       coded in binary as a finite set of natural numbers and conversely. $)
    ackbij1 $p |- F : ( ~P om i^i Fin ) -1-1-onto-> om $=
      ( va vb vc com cpw wceq cv wcel c0 csuc eleq1 cfv wrex ax-mp wb fvelrnb
      cfn cin wf1o wf1 crn dff1o5 ackbij1lem17 wf wss f1f frn mp2b ackbij1lem13
      peano1 ackbij1lem3 fveq2 eqeq1d rcla4ev mp2an wfn f1fn mpbir ackbij1lem18
      adantl suceq eqeq2d rexbidv syl5ibcom rexlimdva 3imtr4g finds ssriv eqssi
      wa mpbir2an ) HIUAUBZHCUCVPHCUDZCUEZHJVPHCUFABCDUGZVRHVQVPHCUHVRHUIVSVPHC
      UJVPHCUKULEHVRFKZVRLMVRLZEKZVRLZWBNZVRLZWCFEWBVTMVROVTWBVROZVTWDVROWFWAWB
      CPZMJZEVPQZMVPLZMCPZMJZWIMHLWJUNMUORABCDUMWHWLEMVPWBMJWGWKMWBMCUPUQURUSCV
      PUTZWAWISVQWMVSVPHCVARZEVPMCTRVBWBHLZGKZCPZWBJZGVPQZVTCPZWDJZFVPQZWCWEWOW
      RXBGVPWOWPVPLZVNWTWQNZJZFVPQZWRXBXCXFWOABWPCFDVCVDWRXEXAFVPWRXDWDWTWQWBVE
      VFVGVHVIWMWCWSSWNGVPWBCTRWMWEXBSWNFVPWDCTRVJVKVLVMVO $.
      $( [18-Nov-2014] $)

    $( The Ackermann bijection, part 1b: the bijection from ~ ackbij1 restricts
       naturally to the powers of particular naturals. $)
    ackbij1b $p |- ( A e. om -> ( F " ~P A ) = ( card ` ~P A ) ) $=
      ( va com wcel cpw cima cfv wn wceq cen wbr cfn wss sylib syl ax-mp wo cin
      ccrd wpss cv imaeq2d breq12d wf1 ackbij1lem17 ackbij2lem1 f1imaen sylancr
      pweq vex pwex vtoclga con0 onfin2 inss2 eqsstri pwfi ficardid ensymg sylc
      sseli entr syl2anc csdm wi ficardom sseldi php3 ex sdomnen syl6 mt2d wral
      cvv wa csuc fvex ackbij1lem3 ackbij1lem12 syl2an word ackbij1lem10 peano1
      elpwi f0cli nnord ordsucsssuc csn ackbij1lem14 ackbij1lem8 eqtr3d sseqtrd
      wb mp2an adantr sucssel mpsyl ralrimiva wfun cdm f1dm syl6sseqr funimass4
      f1fun mpbird sspss orel1 ) CGHZDCIZJZXMUCKZUDZLXPXNXOMZUAZXQXLXPXNXONOZXL
      XNXMNOZXMXONOZXSDFUEZIZJZYCNOZXTFCGYBCMZYDXNYCXMNYFYCXMDYBCUMZUFYGUGYBGHG
      IPUBZGDUHZYCYHQYEABDEUIZYBUJYHGYCDYBFUNUOUKULUPXLXMPHZXOXMNOZYAXLCPHYKGPC
      GUQPUBPURUQPUSUTZVECVARZXLYKYLYNXMVBSXOXMPVCVDXNXMXOVFVGXLXPXNXOVHOZXSLXL
      XOPHZXPYOVIXLGPXOYMXLYKXOGHYNXMVJSVKYPXPYOXOXNVLVMSXNXOVNVOVPXLXNXOQZXRXL
      YQYBDKZXOHZFXMVQZXLYSFXMYRVRHXLYBXMHZVSZYRVTZXOQYSYBDWAUUBUUCCDKZVTZXOUUB
      YRUUDQZUUCUUEQZXLCYHHYBCQUUFUUACWBYBCWHABYBCDEWCWDYRWEZUUDWEZUUFUUGWQYRGH
      UUHYHGYBDABDEWFZWGWIYRWJTUUDGHUUIYHGCDUUJWGWIUUDWJTYRUUDWKWRRXLUUEXOMUUAX
      LCWLDKUUEXOABCDEWMABCDEWNWOWSWPYRXOVRWTXAXBXLDXCZXMDXDZQYQYTWQYIUUKYJYHGD
      XHTXLXMYHUULCUJYIUULYHMYJYHGDXETXFFXMXODXGULXIXNXOXJRXPXQXKVD $.
      $( [18-Nov-2014] $)

    ackbij.g $e |- G = ( x e. _V |-> ( y e. ~P dom x |->
          ( F ` ( x " y ) ) ) ) $.
    $( Lemma for ~ ackbij2 . $)
    ackbij2lem2 $p |- ( A e. om -> ( rec ( G , (/) ) ` A ) :
        ( R1 ` A ) -1-1-onto-> ( card ` ( R1 ` A ) ) ) $=
      ( cr1 cfv ccrd c0 wf1o wceq wb fveq2 syl fveq2d syl2anc com wcel va vb vc
      cv crdg csuc f1oeq1 f1oeq23 bitrd weq f1o0 0ex rdg0 ax-mp r10 card0 eqtri
      fveq2i mp2an bitri mpbir wa cpw cres cima cmpt ccom cfn cin wf1 wss f1of1
      ackbij1 a1i r1fin ficardom ackbij2lem1 f1ores ackbij1b ficardid fvex pwen
      cen wbr cvv wi pwex carden2b eqtrd f1oeq3 mpbid adantr f1opw adantl f1oco
      3syl cdm peano2 fvres eqcomd frsuc dmeq pweqd imaeq1 mpteq12dv dmex mptex
      fvmpt eqidd 3eqtrd f1odm mpteq1 wfn eqid fnmpt mprg f1ofn wf f1of ffvelrn
      sylan imaeq2 imaexg simpr fvco4 3eqtr4d eqfnfvd con0 nnon r1suc mpbird ex
      finds ) UAUDZHIZYOJIZYNEKUEZIZLZKHIZYTJIZKYQIZLZUBUDZHIZUUEJIZUUDYQIZLZUU
      DUFZHIZUUJJIZUUIYQIZLZCHIZUUNJIZCYQIZLZUAUBCYNKMZYSYOYPUUBLZUUCUURYRUUBMY
      SUUSNYNKYQOYOYPYRUUBUGPUURYOYTMYPUUAMUUSUUCNYNKHOZUURYOYTJUUTQYOYTYPUUAUU
      BUHRUIUAUBUJZYSYOYPUUGLZUUHUVAYRUUGMYSUVBNYNUUDYQOYOYPYRUUGUGPUVAYOUUEMYP
      UUFMUVBUUHNYNUUDHOZUVAYOUUEJUVCQYOUUEYPUUFUUGUHRUIYNUUIMZYSYOYPUULLZUUMUV
      DYRUULMYSUVENYNUUIYQOYOYPYRUULUGPUVDYOUUJMYPUUKMUVEUUMNYNUUIHOZUVDYOUUJJU
      VFQYOUUJYPUUKUULUHRUIYNCMZYSYOYPUUPLZUUQUVGYRUUPMYSUVHNYNCYQOYOYPYRUUPUGP
      UVGYOUUNMYPUUOMUVHUUQNYNCHOZUVGYOUUNJUVIQYOUUNYPUUOUUPUHRUIUUCKKKLZUKUUCY
      TUUAKLZUVJUUBKMUUCUVKNKEULUMYTUUAUUBKUGUNYTKMUUAKMUVKUVJNUOUUAKJIKYTKJUOU
      RUPUQYTKUUAKKUHUSUTVAUUDSTZUUHUUMUVLUUHVBZUUMUUEVCZUVNJIZDUUFVCZVDZUAUVNU
      UGYNVEZVFZVGZLZUVMUVPUVOUVQLZUVNUVPUVSLZUWAUVLUWBUUHUVLUVPDUVPVEZUVQLZUWB
      UVLSVCVHVIZSDVJZUVPUWFVKZUWEUWGUVLUWFSDLUWGABDFVMUWFSDVLUNVNUVLUUFSTZUWHU
      VLUUEVHTZUWIUUDVOZUUEVPPZUUFVQPUWFSUVPDVRRUVLUWDUVOMUWEUWBNUVLUWDUVPJIZUV
      OUVLUWIUWDUWMMUWLABUUFDFVSPUVLUUFUUEWCWDZUVPUVNWCWDZUWMUVOMZUVLUWJUWNUWKU
      UEVTPUUFUUEUUDHWAZWBUVNWETUWOUWPWFUUEUWQWGUVPUVNWEWHUNWPWIUWDUVOUVPUVQWJP
      WKWLUUHUWCUVLUUEUUFUUGUAWMWNZUVNUVPUVOUVQUVSWORZUVMUUMUUJUUKUVTLZUWAUVMUU
      LUVTMUUMUWTNUVMUULBUUGWQZVCZUUGBUDZVEZDIZVFZBUVNUXEVFZUVTUVLUULUXFMUUHUVL
      UULUUIYQSVDZIZUUDUXHIZEIZUXFUVLUXIUULUVLUUISTUXIUULMUUDWRUUISYQWSPWTKUUDE
      XAUVLUXKUUGEIZUXFUXFUVLUXJUUGEUUDSYQWSQUXLUXFMZUVLUUGWETZUXMUUDYQWAZAUUGB
      AUDZWQZVCZUXPUXCVEZDIZVFUXFWEEUXPUUGMZBUXRUXTUXBUXEUYAUXQUXAUXPUUGXBXCUYA
      UXSUXDDUXPUUGUXCXDQXEGBUXBUXEUXAUUGUXOXFWGXGXHUNVNUVLUXFXIXJXJWLUVMUXBUVN
      MUXFUXGMUVMUXAUUEUUHUXAUUEMUVLUUEUUFUUGXKWNXCBUXBUVNUXEXLPUVMUCUVNUXGUVTU
      XGUVNXMZUVMUXEWETZUYBBUVNBUVNUXEUXGWEUXGXNZXOUYCUXCUVNTUXDDWAVNXPVNUVMUWA
      UVTUVNXMUWSUVNUVOUVTXQPUVMUCUDZUVNTZVBZUUGUYEVEZDIZUYEUVSIZUVQIZUYEUXGIZU
      YEUVTIZUYGUYKUYIUYGUYKUYJDIZUYIUYGUYJUVPTZUYKUYNMUVMUVNUVPUVSXRZUYFUYOUVM
      UWCUYPUWRUVNUVPUVSXSPUVNUVPUYEUVSXTYAUYJUVPDWSPUYGUYJUYHDUYFUYJUYHMUVMUAU
      YEUVRUYHUVNUVSYNUYEUUGYBUVSXNUXNUYHWETUXOUUGUYEWEYCUNXHWNQWIWTUYFUYLUYIMU
      VMBUYEUXEUYIUVNUXGBUCUJUXDUYHDUXCUYEUUGYBQUYDUYHDWAXHWNUYGUVSUVNXMZUYFUYM
      UYKMUVMUYQUYFUVMUWCUYQUWRUVNUVPUVSXQPWLUVMUYFYDUVNUVQUVSUYEYERYFYGXJUUJUU
      KUULUVTUGPUVLUWTUWANZUUHUVLUUJUVNMZUUKUVOMUYRUVLUUDYHTUYSUUDYIUUDYJPZUVLU
      UJUVNJUYTQUUJUVNUUKUVOUVTUHRWLUIYKYLYM $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij2lem3 $p |- ( A e. om -> ( rec ( G , (/) ) ` A ) C_
        ( rec ( G , (/) ) ` suc A ) ) $=
      ( wcel c0 cfv csuc cr1 cres cv wceq fveq2 fveq2d syl wss cima va com crdg
      vb suceq reseq12d eqeq12d weq res0 r10 reseq2i 0ex rdg0 3eqtr4ri wfn ccrd
      vc wf1o peano2 ackbij2lem2 f1ofn adantr con0 nnon r1sssuc fnssres syl2anc
      wa fveq1d ad2antlr cpw r1suc eleq2d biimpa vex elpw sylib resima2 cdm cvv
      cmpt fvex resex dmeq pweqd imaeq1 mpteq12dv dmex mptex fvmpt ax-mp fveq1i
      pwex fndm eleqtrrd imaeq2 eqid syl5eq wtr r1tr dftr4 sselda f1odm 3eqtr4d
      a1i adantlr eqtrd rdgsuc ad2antrr fvres adantl eqtr4d eqfnfvd finds resss
      ex eqsstrd ) CUBHZCEIUCZJZCKZXSJZCLJZMZYBUANZXSJZYEKZXSJZYELJZMZOIXSJZIKZ
      XSJZILJZMZOUDNZXSJZYPKZXSJZYPLJZMZOZYSYRKZXSJZYRLJZMZOZXTYDOUAUDCYEIOZYFY
      KYJYOYEIXSPUUHYHYMYIYNUUHYGYLXSYEIUEQYEILPUFUGUAUDUHZYFYQYJUUAYEYPXSPUUIY
      HYSYIYTUUIYGYRXSYEYPUEQYEYPLPUFUGYEYROZYFYSYJUUFYEYRXSPUUJYHUUDYIUUEUUJYG
      UUCXSYEYRUEQYEYRLPUFUGYECOZYFXTYJYDYECXSPUUKYHYBYIYCUUKYGYAXSYECUEQYECLPU
      FUGYMIMIYOYKYMUIYNIYMUJUKIEULUMUNYPUBHZUUBUUGUULUUBVHZUQUUEYSUUFUULYSUUEU
      OZUUBUULUUEUUEUPJZYSURZUUNUULYRUBHZUUPYPUSZABYRDEFGUTRZUUEUUOYSVARZVBUULU
      UFUUEUOZUUBUULUUDUUCLJZUOZUUEUVBSZUVAUULUVBUVBUPJZUUDURZUVCUULUUCUBHZUVFU
      ULUUQUVGUURYRUSRABUUCDEFGUTRUVBUVEUUDVARUULYRVCHZUVDUULUUQUVHUURYRVDRZYRV
      ERUVBUUEUUDVFVGVBUUMUQNZUUEHZVHZUVJYSJZUVJUUDJZUVJUUFJZUVLUVJYQEJZJZUVJYS
      EJZJZUVMUVNUVLUVQUVJUUAEJZJZUVSUUBUVQUWAOUULUVKUUBUVJUVPUVTYQUUAEPVIVJUUL
      UVKUWAUVSOUUBUULUVKVHZUUAUVJTZDJZYSUVJTZDJZUWAUVSUWBUWCUWEDUWBUVJYTSZUWCU
      WEOUWBUVJYTVKZHZUWGUULUVKUWIUULUUEUWHUVJUULYPVCHZUUEUWHOYPVDZYPVLRVMVNZUV
      JYTUQVOVPVQYSUVJYTVRRQUWBUWAUVJBUUAVSZVKZUUABNZTZDJZWAZJZUWDUVJUVTUWRUUAV
      THUVTUWROYSYTYRXSWBZWCZAUUABANZVSZVKZUXBUWOTZDJZWAZUWRVTEUXBUUAOZBUXDUXFU
      WNUWQUXHUXCUWMUXBUUAWDWEUXHUXEUWPDUXBUUAUWOWFQWGGBUWNUWQUWMUUAUXAWHWMWIWJ
      WKWLUWBUVJUWNHUWSUWDOUWBUVJUWHUWNUWLUULUWNUWHOUVKUULUWMYTUULUUAYTUOZUWMYT
      OUULUUNYTUUESZUXIUUTUULUWJUXJUWKYPVERUUEYTYSVFVGYTUUAWNRWEVBWOBUVJUWQUWDU
      WNUWRBUQUHZUWPUWCDUWOUVJUUAWPQUWRWQUWCDWBWJRWRUWBUVSUVJBYSVSZVKZYSUWOTZDJ
      ZWAZJZUWFUVJUVRUXPYSVTHUVRUXPOUWTAYSUXGUXPVTEUXBYSOZBUXDUXFUXMUXOUXRUXCUX
      LUXBYSWDWEUXRUXEUXNDUXBYSUWOWFQWGGBUXMUXOUXLYSUWTWHWMWIWJWKWLUWBUVJUXMHUX
      QUWFOUWBUVJUUEVKZUXMUULUUEUXSUVJUULUUEWSZUUEUXSSUXTUULYRWTXEUUEXAVQXBUULU
      XMUXSOUVKUULUXLUUEUULUUPUXLUUEOUUSUUEUUOYSXCRWEVBWOBUVJUXOUWFUXMUXPUXKUXN
      UWEDUWOUVJYSWPQUXPWQUWEDWBWJRWRXDXFXGUULUVMUVQOUUBUVKUULUVJYSUVPUULUWJYSU
      VPOUWKIYPEXHRVIXIUULUVNUVSOUUBUVKUULUVJUUDUVRUULUVHUUDUVROUVIIYREXHRVIXIX
      DUVKUVOUVNOUUMUVJUUEUUDXJXKXLXMXPXNYDYBSXRYBYCXOXEXQ $.
      $( [18-Nov-2014] $)

    $( Lemma for ~ ackbij2 . $)
    ackbij2lem4 $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) ->
        ( rec ( G , (/) ) ` B ) C_ ( rec ( G , (/) ) ` A ) ) $=
      ( va vb c0 cfv cv wss wceq fveq2 sseq2d com wcel wa crdg csuc ackbij2lem3
      weq ssid a1i ad2antrr sstr2 syl5com findsg ) DFKUAZLZIMZUKLZNULULNZULJMZU
      KLZNZULUPUBZUKLZNZULCUKLZNIJCDUMDOUNULULUMDUKPQIJUDUNUQULUMUPUKPQUMUSOUNU
      TULUMUSUKPQUMCOUNVBULUMCUKPQUODRSZULUEUFUPRSZVCTDUPNZTUQUTNZURVAVDVFVCVEA
      BUPEFGHUCUGULUQUTUHUIUJ $.
      $( [18-Nov-2014] $)

    ackbij.h $e |- H = U. ( rec ( G , (/) ) " om ) $.
    $( The Ackermann bijection, part 2: hereditarily finite sets can be
       represented by recursive binary notation. $)
    ackbij2 $p |- H : U. ( R1 " om ) -1-1-onto-> om $=
      ( va vb cr1 com wf1o wceq cfv wss wcel cfn con0 ax-mp vc cima cuni c0 wf1
      crdg dff1o5 cv ciun wo wral wa fveq2 fvex fun11iun ccrd ackbij2lem2 f1of1
      crn syl r1fin ficardom word ordom ordelss mpan 3syl f1ss nnord ordtri2or2
      syl2anc syl2an wi ackbij2lem4 ex ancoms orim12d mpd ralrimiva jca mprg wb
      wfun wfn rdgfnon fnfun funiunfv eqcomd f1eq1 mp2b f1eq2 bitri mpbir rnuni
      r1fnon wrex wex eliun df-rex omsson fvelimab mp2an wfo f1ofo forn sylancr
      eqsstrd rneq sseq1d syl5ibcom rexlimiv sylbi sselda exlimiv csuc cdm fndm
      peano2 sseqtr4i funfvima2 cardnn cdom wbr onssr1 cvv vex sucex ssdomg cin
      nnon onfin2 inss2 eqsstri sseli ficarddom mpbid eqsstr3d sucssel eleqtrrd
      eleq1 eleq2d anbi12d cla4ev impbii 3bitri eqriv eqtri mpbir2an f1oeq1 ) K
      LUBUCZLEMZUUJLDUDUFZLUBZUCZMZUUOUUJLUUNUEZUUNUSZLNUUJLUUNUGUUPILIUHZKOZUI
      ZLILUURUULOZUIZUEZUUSLUVAUEZUVAJUHZUULOZPZUVFUVAPZUJZJLUKZULUVCILIJLUVAUV
      FUUSLUURUVEUULUMUURUULUNUOUURLQZUVDUVJUVKUUSUUSUPOZUVAUEZUVLLPZUVDUVKUUSU
      VLUVAMUVMABUURCDFGUQUUSUVLUVAURUTUVKUUSRQUVLLQZUVNUURVAUUSVBLVCZUVOUVNVDL
      UVLVEVFVGUUSUVLLUVAVHVKUVKUVIJLUVKUVELQZULZUURUVEPZUVEUURPZUJZUVIUVKUURVC
      UVEVCUWAUVQUURVIUVEVIUURUVEVJVLUVRUVSUVGUVTUVHUVQUVKUVSUVGVMUVQUVKULUVSUV
      GABUVEUURCDFGVNVOVPUVRUVTUVHABUURUVECDFGVNVOVQVRVSVTWAUUPUUJLUVBUEZUVCUUL
      WCZUUNUVBNUUPUWBWBUULSWDZUWCUDDWEZSUULWFTZUWCUVBUUNILUULWGWHUUJLUUNUVBWIW
      JKWCZUUJUUTNUWBUVCWBKSWDUWGWOSKWFTUWGUUTUUJILKWGWHUUJUUTLUVBWKWJWLWMUUQIU
      UMUURUSZUIZLIUUMWNJUWILUVEUWIQUVEUWHQZIUUMWPUURUUMQZUWJULZIWQZUVQIUVEUUMU
      WHWRUWJIUUMWSUWMUVQUWLUVQIUWKUWHLUVEUWKUAUHZUULOZUURNZUALWPZUWHLPZUWDLSPU
      WKUWQWBUWEWTUASLUURUULXAXBUWPUWRUALUWNLQZUWOUSZLPUWPUWRUWSUWTUWNKOZUPOZLU
      WSUXAUXBUWOMUXAUXBUWOXCUWTUXBNABUWNCDFGUQUXAUXBUWOXDUXAUXBUWOXEVGUWSUVPUX
      BLQZUXBLPVDUWSUXARQUXCUWNVAUXAVBUTLUXBVEXFXGUWPUWTUWHLUWOUURXHXIXJXKXLXMX
      NUVQUVEXOZUULOZUUMQZUVEUXEUSZQZUWMUVQUXDLQZUXFUVEXRZUWCLUULXPZPUXIUXFVMUW
      FLSUXKWTUWDUXKSNUWESUULXQTXSLUXDUULXTXBUTUVQUVEUXDKOZUPOZUXGUVQUXIUXDUXMP
      ZUVEUXMQZUXJUXIUXDUXDUPOZUXMUXDYAUXIUXDUXLYBYCZUXPUXMPZUXIUXDSQUXDUXLPZUX
      QUXDYJUXDYDUXDYEQUXSUXQVMUVEJYFZYGUXDUXLYEYHTVGUXIUXDRQUXLRQUXQUXRWBLRUXD
      LSRYIRYKSRYLYMYNUXDVAUXDUXLYOVKYPYQUVEYEQUXNUXOVMUXTUVEUXMYEYRTVGUVQUXLUX
      MUXEMZUXLUXMUXEXCUXGUXMNUVQUXIUYAUXJABUXDCDFGUQUTUXLUXMUXEXDUXLUXMUXEXEVG
      YSUWLUXFUXHULIUXEUXDUULUNUURUXENZUWKUXFUWJUXHUURUXEUUMYTUYBUWHUXGUVEUURUX
      EXHUUAUUBUUCVKUUDUUEUUFUUGUUHEUUNNUUKUUOWBHUUJLEUUNUUITWM $.
      $( [18-Nov-2014] $)
  $}

  ${
    $d a b c d e f $.

    $( The set of hereditarily finite sets is countable.  See ~ ackbij2 for an
       explicit bijection that works without Infinity. $)
    r1omNEW $p |- ( R1 ` om ) ~~ om $=
      ( vc vd ve vf va vb com cvv cr1 cfv cen cv cpw cima cmpt ccrd weq cbvmptv
      ccsum fveq2d wcel wbr cdm cfn cin crdg cuni wf1o mpteq1 pweq syl6eq pweqd
      c0 dmeq imaeq1 mpteq12dv eqid ackbij2 wceq wb ciun wlim limom r1lim mpan2
      imaeq2 wfun con0 wfn r1fnon fnfun ax-mp funiunfv f1oeq2 mpbiri fvex f1oen
      syl wn enref brprc pm2.61i ) GHUAZGIJZGKUBZWCWDGAHBALZUCZMZWFBLZNZCGMUDUE
      ZDCLZDLZMZOZSJZPJZOZJZOZOZUMUFGNUGZUHZWEWCXCIGNUGZGXBUHZEFWRXAXBCEWKWQFEL
      ZFLZMZOZSJZPJCEQZWPXJPXKWOXISXKWODXFWNOXIDWLXFWNUIDFXFWNXHWMXGUJRUKTTRAEH
      WTFXFUCZMZXFXGNZWRJZOZAEQZWTBXMXFWINZWRJZOXPXQBWHWSXMXSXQWGXLWFXFUNULXQWJ
      XRWRWFXFWIUOTUPBFXMXSXOBFQXRXNWRWIXGXFVFTRUKRXBUQURWCWDXDUSXCXEUTWCWDEGXF
      IJVAZXDWCGVBWDXTUSVCEGHVDVEIVGZXTXDUSIVHVIYAVJVHIVKVLEGIVMVLUKWDXDGXBVNVR
      VOWDGXBGIVPZVQVRWCVSWEWDWDKUBWDYBVTWDGKWAVOWB $.
      $( [18-Nov-2014] $)
  $}

$( (End of Stefan O'Rear's mathbox.) $)
