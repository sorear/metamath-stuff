$[ set.mm $]

$( early warmup proofs.  I may find a use for Id ` x. later $)

wu0 $p |- ( ( ZZ ^m ( 1 ... 0 ) ) X. { 0 } ) e. ( ZZ ^m ( ZZ ^m ( 1 ... 0 ) ) ) $= ( cc0 csn cz c1 cfz co cmap cxp wss wcel 0z snssi ax-mp zex ovex mapss wf elexi fconst snex elmap mpbir sselii ) ABZCDAEFZGFZGFZCUFGFZUFUDHZUDCIZUGUHIACJUJKACLMUDCUFNCUEGOZPMUIUGJUFUDUIQUFAACKRSUDUFUIATUKUAUBUC $.
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

$( ---- NUMBER THEORY ---- $)
$( Special Pell equations and Kummer's theorem.  Prove that certain polynomial identities are equivalent to exponential and bitwise ones. $)

$( Another form of the pigeonhole principle. $)

${
    $d x y F $.  $d x y A $.
    fphp $p |- ( ( ( A e. _V /\ B e. _V /\ B ~< A ) /\ F : A --> B ) -> E. x e. A E. y e. A ( x =/= y /\ ( F ` x ) = ( F ` y ) ) ) $=
      ( cvv wcel csdm wbr w3a wf wa cv cfv wral wn wrex 3bitri rexbii rexnal weq
      wceq wi wne cdom domnsym con2i 3ad2ant3 adantr wf1 simpll1 biimpri adantll
      dff13 f1domg sylc mtand ancom df-ne anbi2i annim sylibr ) CFGZDFGZDCHIZJZC
      DEKZLZAMZENBMZENUBZABUAZUCZBCOZACOZPZVIVJUDZVKLZBCQZACQZVHVOCDUEIZVFWAPZVG
      VEVCWBVDWAVECDUFUGUHUIVHVOLVCCDEUJZWAVCVDVEVGVOUKVGVOWCVFWCVGVOLABCDEUNULU
      MCDFEUOUPUQVTVMPZBCQZACQVNPZACQVPVSWEACVRWDBCVRVKVQLVKVLPZLWDVQVKURVQWGVKV
      IVJUSUTVKVLVARSSWEWFACVMBCTSVNACTRVB $.
      $( [11-Sep-2014] $)
$}

$( Pigeonhole principle expressed with implicit substitution.  Can this be done without the extra variable? $)
${
    $d ph x y z $.  $d A x y z $.  $d B z $.  $d C x y $.  $d D y z $.  $d E x z $.
    fphpd.1 $e |- ( ph -> A e. _V ) $.
    fphpd.2 $e |- ( ph -> B e. _V ) $.
    fphpd.3 $e |- ( ph -> B ~< A ) $.
    fphpd.4 $e |- ( ( ph /\ z e. A ) -> C e. B ) $.
    fphpd.5 $e |- ( z = x -> C = D ) $.
    fphpd.6 $e |- ( z = y -> C = E ) $.

    fphpd $p |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ D = E ) ) $=
      ( cv wceq wa wrex wcel wne cmpt cfv cvv csdm wbr eqid fmptd syl31anc simpr
      wf wi weq eleq1 anbi2d eleq1d imbi12d chvarv fvmptg syl2anc adantr adantlr
      fphp eqeq12d rexbidva mpbid ) ABPZCPZUAZVGDEGUBZUCZVHVJUCZQZRZCESZBESZVIHI
      QZRZCESZBESAEUDTFUDTFEUEUFEFVJUKVPJKLADEGFVJMVJUGZUHBCEFVJVCUIAVOVSBEAVGET
      ZRZVNVRCEWBVHETZRZVMVQVIWDVKHVLIWBVKHQZWCWBWAHFTZWEAWAUJADPZETZRZGFTZULZWB
      WFULDBDBUMZWIWBWJWFWLWHWAAWGVGEUNUOWLGHFNUPUQMURDVGGHEFVJNVTUSUTVAAWCVLIQZ
      WAAWCRZWCIFTZWMAWCUJWKWNWOULDCDCUMZWIWNWJWOWPWHWCAWGVHEUNUOWPGIFOUPUQMURDV
      HGIEFVJOVTUSUTVBVDUOVEVEVF $.
      $( [11-Sep-2014] $)
$}

$( Pigeonhole principle for sets of real numbers with an ordering constraint wlog. $)
${
    $d ph x y z a b c $.  $d A x y z a b c $.  $d B z a b c $.  $d C x y a b c $.  $d D y z a b c $.  $d E x z a b c $.
    fphpdo.1 $e |- ( ph -> A C_ RR ) $.
    fphpdo.2 $e |- ( ph -> B e. _V ) $.
    fphpdo.3 $e |- ( ph -> B ~< A ) $.
    fphpdo.4 $e |- ( ( ph /\ z e. A ) -> C e. B ) $.
    fphpdo.5 $e |- ( z = x -> C = D ) $.
    fphpdo.6 $e |- ( z = y -> C = E ) $.

    fphpdo $p |- ( ph -> E. x e. A E. y e. A ( x < y /\ D = E ) ) $=
      ( vb wceq wa clt wcel vc va cv wne cmpt cfv wrex wbr wss cvv reex ssex syl
      cr wf eqid fmptd ffvelrn sylan fveq2 fphpd wo sselda adantrr adantr lttri2
      wb adantrl syl2anc simplrl anass1rs simplrr simpr simplr weq breq1 anbi12d
      eqeq1d breq2 eqeq2d rcla42ev syl112anc ex eqcomd jaod eleq1 anbi2d imbi12d
      wi eleq1d chvarv fvmptg adantlr eqeq12d biimpd anim2d reximdva syld sylbid
      expimpd ancomsd rexlimdvva mpd ) APUCZUAUCZUDZXDDEGUEZUFZXEXGUFZQZRZUAEUGP
      EUGBUCZCUCZSUHZHIQZRZCEUGZBEUGZAPUAUBEFUBUCZXGUFZXHXIAEUNUIEUJTJEUNUKULUMK
      LAEFXGUOXSETXTFTADEGFXGMXGUPZUQEFXSXGURUSXSXDXGUTXSXEXGUTVAAXKXRPUAEEAXDET
      ZXEETZRZRZXJXFXRYEXJXFXRYEXJRZXFXDXESUHZXEXDSUHZVBZXRYFXDUNTZXEUNTZXFYIVGY
      EYJXJAYBYJYCAEUNXDJVCVDVEYEYKXJAYCYKYBAEUNXEJVCVHVEXDXEVFVIYFYIXNXLXGUFZXM
      XGUFZQZRZCEUGZBEUGZXRYFYGYQYHYFYGYQYFYGRYBYCYGXJYQYEYGXJYBAYBYCYGXJRZVJVKY
      EYGXJYCAYBYCYRVLVKYFYGVMYEXJYGVNYOYRXDXMSUHZXHYMQZRBCXDXEEEBPVOZXNYSYNYTXL
      XDXMSVPUUAYLXHYMXLXDXGUTVRVQCUAVOZYSYGYTXJXMXEXDSVSUUBYMXIXHXMXEXGUTVTVQWA
      WBWCYFYHYQYFYHRZYCYBYHXIXHQZYQYEYHXJYCAYBYCYHXJRZVLVKYEYHXJYBAYBYCUUEVJVKY
      FYHVMUUCXHXIYEXJYHVNWDYOYHUUDRXEXMSUHZXIYMQZRBCXEXDEEBUAVOZXNUUFYNUUGXLXEX
      MSVPUUHYLXIYMXLXEXGUTVRVQCPVOZUUFYHUUGUUDXMXDXESVSUUIYMXHXIXMXDXGUTVTVQWAW
      BWCWEYEYQXRWIZXJAUUJYDAYPXQBEAXLETZRZYOXPCEUULXMETZRZYNXOXNUUNYNXOUUNYLHYM
      IUUNUUKHFTZYLHQAUUKUUMVNUULUUOUUMADUCZETZRZGFTZWIZUULUUOWIDBDBVOZUURUULUUS
      UUOUVAUUQUUKAUUPXLEWFWGUVAGHFNWJWHMWKVEDXLGHEFXGNYAWLVIUUNUUMIFTZYMIQUULUU
      MVMAUUMUVBUUKUUTAUUMRZUVBWIDCDCVOZUURUVCUUSUVBUVDUUQUUMAUUPXMEWFWGUVDGIFOW
      JWHMWKWMDXMGIEFXGOYAWLVIWNWOWPWQWQVEVEWRWSWTXAXBXC $.
      $( [12-Sep-2014] $)
$}

${
    $( ~ cfslb2n transfered to arbitrary sets by cardinality. $)
    $( a direct proof might be much shorter? $)
    $d a b c d e f x A $.
    $d a b c d e f x B $.
    encfslb2n.1 $e |- A e. _V $.
    encfslb2n $p |- ( ( Lim ( card ` A ) /\ A. x e. B ( x C_ A /\ x ~< ( cf ` ( card ` A ) ) ) /\ B ~< ( cf ` ( card ` A ) ) ) -> U. B =/= A ) $=
      ( vb vc vd ve vf cv wss csdm wbr wa cvv cima wcel wceq ex ax-mp va cfv ccf
      ccrd wlim wral w3a wf1o wex cuni wne cen cardid ensymi fvex bren mpbi cmpt
      simpl1 wrex wfun wi funmpt a1i fvelima syl crn imassrn f1ofo adantl adantr
      wfo forn syl5sseq cdom imadomg mpan9 simpr simpll2 weq sseq1 breq1 anbi12d
      f1ofun rcla4v sylc simprd domsdomtr syl2anc jca wb vex imaeq2 imaexg fvmpt
      eqeq1i sylbi syl5ibcom rexlimdva ralrimiv relsdom brrelexi 3ad2ant3 simpl3
      eqid syld cfslb2n imp syl21anc simplr ad2antrr ciun wel ccnv wf1 ad3antrrr
      mpan simp1 f1of1 elssuni simpll3 sseqtrd f1imacnv eqeltrd id eqtr3d eleq1d
      imaeq2d mpbid syl5 impr simpllr eleqtrd eqcomd eleq2d rcla4ev fveq2 3eqtrd
      exlimdv sylancl eqeq1d wfn rgenw fnmpt fvelimab mpbird eleq2 cla4ev impbid
      ssv eleq1 eluni eliun 3bitr4g eqrdv imauni syl6eqr simp3 cdm f1odm imadmrn
      3ad2ant1 3syl syl3anc necon3d mpd mpi ) BUDUBZUEZAJZBKZUVJUVHUCUBZLMZNZACU
      FZCUVLLMZUGZBUVHUAJZUHZUAUIZCUJZBUKZBUVHULMUVTUVHBDBUMUNBUVHUABUDUOZUPUQUV
      QUVSUWBUAUVQUVSUWBUVQUVSNZEOUVREJZPZURZCPZUJZUVHUKZUWBUWDUVIFJZUVHKZUWKUVL
      LMZNZFUWHUFZUWHUVLLMZUWJUVIUVOUVPUVSUSUWDUWNFUWHUWDUWKUWHQZGJZUWGUBZUWKRZG
      CUTZUWNUWDUWGVAZUWQUXAVBUXBUWDEOUWFVCZVDZUXBUWQUXAGUWKCUWGVESVFUWDUWTUWNGC
      UWDUWRCQZNZUVRUWRPZUVHKZUXGUVLLMZNZUWTUWNUXFUXHUXIUXFUVRVGZUXGUVHUVRUWRVHU
      WDUXKUVHRZUXEUVSUXLUVQUVSBUVHUVRVLZUXLBUVHUVRVIZBUVHUVRVMZVFVJVKVNUXFUXGUW
      RVOMZUWRUVLLMZUXIUWDUVRVAZUXEUXPUVSUXRUVQBUVHUVRWDVJUWRCUVRVPVQUXFUWRBKZUX
      QUXFUXEUVOUXSUXQNZUWDUXEVRUVIUVOUVPUVSUXEVSUVNUXTAUWRCAGVTUVKUXSUVMUXQUVJU
      WRBWAUVJUWRUVLLWBWCWEWFWGUXGUWRUVLWHWIWJUWTUXGUWKRZUXJUWNWKUWSUXGUWKUWROQU
      WSUXGRGWLEUWRUWFUXGOUWGUWEUWRUVRWMUWGXEZUVROQZUXGOQUAWLZUVRUWROWNTWOTWPUYA
      UXHUWLUXIUWMUXGUWKUVHWAUXGUWKUVLLWBWCWQWRWSXFWTUWDUWHCVOMZUVPUWPUWDCOQZUXB
      UYEUVQUYFUVSUVPUVIUYFUVOCUVLLXAXBXCZVKUXDCOUWGVPWFUVIUVOUVPUVSXDUWHCUVLWHW
      IUVIUWONUWPUWJFUVHUWHUWCXGXHXIUWDUWABUWIUVHUWDUWABRZUWIUVHRZUWDUYHNUVSUYFU
      YHUYIUVQUVSUYHXJUVQUYFUVSUYHUYGXKUWDUYHVRUVSUYFUYHUGZUWIUVRUWAPZUVRBPZUVHU
      YJUWIFCUVRUWKPZXLZUYKUYJGUWIUYNUYJGHXMZHJZUWHQZNZHUIZUWRUYMQZFCUTZUWRUWIQU
      WRUYNQUYJUYSVUAUYJUYRVUAHUYJUYRVUAUYJUYRNUVRXNZUYPPZCQZUWRUVRVUCPZQZVUAUYJ
      UYOUYQVUDUYQIJZUWGUBZUYPRZICUTZUYJUYONZVUDUXBUYQVUJUXCIUYPCUWGVEXQZVUKVUIV
      UDICVUKVUGCQZNZVUIVUDVUNVUINZVUBUVRVUGPZPZCQZVUDVUOVUQVUGCVUOBUVHUVRXOZVUG
      BKZVUQVUGRVUOUVSVUSUYJUVSUYOVUMVUIUVSUYFUYHXRZXPBUVHUVRXSVFVUNVUTVUIVUNVUG
      UWABVUMVUGUWAKVUKVUGCXTVJUVSUYFUYHUYOVUMYAYBVKBUVHVUGUVRYCWIZVUKVUMVUIXJYD
      VUIVURVUDWKVUNVUIVUQVUCCVUIVUPUYPVUBVUIVUHVUPUYPVUHVUPRZVUIVUGOQVVCIWLEVUG
      UWFVUPOUWGUWEVUGUVRWMUYBUYCVUPOQUYDUVRVUGOWNTWOTZVDVUIYEYFYHZYGVJYISWSYJYK
      UYJUYOUYQVUFUYQVUJVUKVUFVULVUKVUIVUFICVUNVUIVUFVUOUWRUVRVUQPZQZVUFVUOUWRVU
      PVVFVUOUWRUYPVUPUYJUYOVUMVUIYLVUOVUHUYPVUPVUNVUIVRVVCVUOVVDVDYFYMVUOVUGVUQ
      UVRVUOVUQVUGVVBYNYHYMVUIVVGVUFWKVUNVUIVVFVUEUWRVUIVUQVUCUVRVVEYHYOVJYISWSY
      JYKUYTVUFFVUCCUWKVUCRUYMVUEUWRUWKVUCUVRWMYOYPWISYSUYJUYTUYSFCUYJUWKCQZNZUY
      TUYSVVIUYTNZUYTUYMUWHQZUYSVVIUYTVRVVJVVKVUHUYMRZICUTZVVJVVHUWKUWGUBZUYMRZV
      VMUYJVVHUYTXJUWKOQVVOFWLEUWKUWFUYMOUWGUWEUWKUVRWMUYBUYCUYMOQUYDUVRUWKOWNTZ
      WOTVVLVVOIUWKCIFVTVUHVVNUYMVUGUWKUWGYQUUAYPYTVVJUWGOUUBZCOKVVKVVMWKVVQVVJU
      WFOQZEOUFVVQVVREOUYCVVRUYDUVRUWEOWNTUUCEOUWFUWGOUYBUUDTVDCUUJIOCUYMUWGUUEY
      TUUFUYRUYTVVKNHUYMVVPUYPUYMRUYOUYTUYQVVKUYPUYMUWRUUGUYPUYMUWHUUKWCUUHWISWS
      UUIHUWRUWHUULFUWRCUYMUUMUUNUUOFUVRCUUPUUQUYJUWABUVRUVSUYFUYHUURYHUYJUYLUVR
      UVRUUSZPZUXKUVHUYJBVVSUVRUVSUYFBVVSRUYHUVSVVSBBUVHUVRUUTYNUVBYHVVTUXKRUYJU
      VRUVAVDUYJUVSUXMUXLVVAUXNUXOUVCYRYRUVDSUVEUVFSYSUVG $.
      $( [11-Sep-2014] $)

$}

${
    $d A a b c d e y $.
    $d B a b c d e y $.
    $d C a b c d e y $.
    fiphp1 $p |- ( ( ( A e. _V /\ Lim ( card ` A ) /\ B ~< ( cf ` ( card `
        A ) ) ) /\ C : A --> B ) -> E. y e. B ( cf ` ( card ` A ) ) ~<_ ( `'
        C " { y } ) ) $=
      ( vb va vc vd cvv wcel cfv csdm wbr wa cima wceq adantr wb syl2anc a1i ccf
      ccrd wlim w3a wf ccnv cv csn cdom wrex wn wral cmpt cuni wne simp1 relsdom
      brrelexi 3ad2ant3 simpr wel wex wfn wss simpl3 fex cnvexg imaexg ralrimiva
      eluni 3syl eqid fnmpt syl ssid fvelimab anbi2d exbidv simp3 imaeq2d fvmptg
      weq sneq eqeq1d rexbidva crn imassrn cdm df-rn dmcnvcnv fdm 3eqtrd 3sstr3d
      ad3antrrr simpllr ex rexlimdva expimpd exlimdv eleqtrrd wfun ffun funfvbrb
      sseldd mpbid vex eliniseg ax-mp sylibr ffvelrn 3ad2antl3 eqidd rcla4ev jca
      fvex eleq2 eqeq2 rexbidv anbi12d cla4egv sylc impbid 3bitrd syl5bb syl3anc
      eqrdv nne simpll1 simpll2 funmpt mpan adantl syl5sseq simplr breq1d rcla4v
      fvelima anass1rs wi breq2d sseq1 breq1 syl5 ralrimiv ad2antrr imadomg ee10
      eqtr3d simpll3 domsdomtr 3jca fveq2 limeq fveq2d ralbidv 3anbi123d imbi12d
      sseq2 neeq2 encfslb2n vtoclg mtand rexnal domtri mpbird ) BIJZBUBKZUCZCUVG
      UAKZLMZUDZBCDUEZNZUVIDUFZAUGZUHZOZUIMZACUJZUVQUVILMZUKZACUJZUVMUVTACULZUKU
      WBUVMUWCECUVNEUGZUHZOZUMZCOZUNZBUOZUVMUWIBPZUWJUKUVMUVFCIJZUVLUWKUVKUVFUVL
      UVFUVHUVJUPQZUVKUWLUVLUVJUVFUWLUVHCUVILUQURUSZQUVKUVLUTZUVFUWLUVLUDZFUWIBF
      UGZUWIJFGVAZGUGZUWHJZNZGVBZUWPUWQBJZGUWQUWHVJUWPUXBUWRHUGZUWGKZUWSPZHCUJZN
      ZGVBUWRUVNUXDUHZOZUWSPZHCUJZNZGVBZUXCUWPUXAUXHGUWPUWTUXGUWRUWPUWGCVCZCCVDZ
      UWTUXGRUWPUWFIJZECULUXOUWPUXQECUWPUWDCJZNZDIJZUVNIJZUXQUXSUVLUVFUXTUVFUWLU
      VLUXRVEUWPUVFUXRUVFUWLUVLUPZQBCIDVFZSDIVGZUVNUWEIVHVKVIECUWFUWGIUWGVLZVMVN
      UXPUWPCVOTHCCUWSUWGVPSVQVRUWPUXHUXMGUWPUXGUXLUWRUWPUXFUXKHCUWPUXDCJZNZUXEU
      XJUWSUYGUYFUXJIJZUXEUXJPUWPUYFUTUWPUYHUYFUWPUXTUYAUYHUWPUVLUVFUXTUVFUWLUVL
      VSUYBUYCSZUYDUVNUXIIVHVKQEUXDUWFUXJCIUWGEHWBUWEUXIUVNUWDUXDWCVTUYEWASWDWEV
      QVRUWPUXNUXCUWPUXMUXCGUWPUWRUXLUXCUWPUWRNZUXKUXCHCUYJUYFNZUXKUXCUYKUXKNZUW
      SBUWQUYLUXJUVNWFZUWSBUXJUYMVDUYLUVNUXIWGTUYKUXKUTUWPUYMBPZUWRUYFUXKUWPUYMU
      VNUFWHZDWHZBUYMUYOPZUWPUVNWIZTUYOUYPPZUWPDWJZTUVLUVFUYPBPZUWLBCDWKZUSZWLWN
      WMUWPUWRUYFUXKWOXDWPWQWRWSUWPUXCUXNUWPUXCNZUVNUWQDKZUHZOZIJZUWQVUGJZUXJVUG
      PZHCUJZNZUXNUWPVUHUXCUWPUXTUYAVUHUYIUYDUVNVUFIVHVKQVUDVUIVUKVUDUWQVUEDMZVU
      IVUDUWQUYPJZVUMVUDUWQBUYPUWPUXCUTUWPVUAUXCVUCQWTVUDDXAZVUNVUMRUWPVUOUXCUVL
      UVFVUOUWLBCDXBUSQUWQDXCVNXEVUEIJVUIVUMRUWQDXODVUEUWQIFXFZXGXHXIVUDVUECJZVU
      GVUGPZVUKUVLUVFUXCVUQUWLBCUWQDXJXKVUDVUGXLVUJVURHVUECUXDVUEPZUXJVUGVUGVUSU
      XIVUFUVNUXDVUEWCVTWDXMSXNUXMVULGVUGIUWSVUGPZUWRVUIUXLVUKUWSVUGUWQXPVUTUXKV
      UJHCUWSVUGUXJXQXRXSXTYAWPYBYCYDYFYEUWIBYGXIUVMUWCNZUVFUVHUWSBVDZUWSUVILMZN
      ZGUWHULZUWHUVILMZUDZUWJUVFUVHUVJUVLUWCYHVVAUVHVVEVVFUVFUVHUVJUVLUWCYIVVAVV
      DGUWHUWTUWQUWGKZUWSPZFCUJZVVAVVDUWGXAZUWTVVJECUWFYJZFUWSCUWGYQYKVVAVVIVVDF
      CVVAUWQCJZNZVVIVVDVVNVVINZUVNUWQUHZOZBVDZVVQUVILMZNZVVDVVOVVRVVSVVOUYMVVQB
      UVNVVPWGUVMUYNUWCVVMVVIUVMUYMUYOUYPBUYQUVMUYRTUYSUVMUYTTUVLVUAUVKVUBYLWLWN
      YMVVOVVMUWCVVSVVAVVMVVIYNZUVMUWCVVMVVIWOUVTVVSAUWQCAFWBZUVQVVQUVILVWBUVPVV
      PUVNUVOUWQWCVTYOYPYAXNVVOVVQUWSPZVVTVVDRVVOVVHVVQUWSVVOVVMVVQIJZVVHVVQPVWA
      VVNVWDVVIVVNUXTUYAVWDVVNUVLUVFUXTUVKUVLUWCVVMWOUVMVVMUWCUVFUVFUVHUVJUVLVVM
      UWCNYHYRUYCSUYDUVNVVPIVHVKQEUWQUWFVVQCIUWGEFWBUWEVVPUVNUWDUWQWCVTUYEWASVVN
      VVIUTUUHVWCVVRVVBVVSVVCVVQUWSBUUAVVQUWSUVILUUBXSVNXEWPWQUUCUUDVVAUWHCUIMZU
      VJVVFVVAUWLVVKVWEUVKUWLUVLUWCUWNUUEVVLCIUWGUUFUUGUVFUVHUVJUVLUWCUUIUWHCUVI
      UUJSUUKUWQUBKZUCZUWSUWQVDZUWSVWFUAKZLMZNZGUWHULZUWHVWILMZUDZUWIUWQUOZYSVVG
      UWJYSFBIUWQBPZVWNVVGVWOUWJVWPVWGUVHVWLVVEVWMVVFVWPVWFUVGPVWGUVHRUWQBUBUULZ
      VWFUVGUUMVNVWPVWKVVDGUWHVWPVWHVVBVWJVVCUWQBUWSUURVWPVWIUVIUWSLVWPVWFUVGUAV
      WQUUNZYTXSUUOVWPVWIUVIUWHLVWRYTUUPUWQBUWIUUSUUQGUWQUWHVUPUUTUVAYAUVBUVTACU
      VCXIUVMUXTUVSUWBRUVMUVLUVFUXTUWOUWMUYCSUXTUVRUWAACUXTUVIIJZUVQIJZUVRUWARVW
      SUXTUVGUAXOTUXTUYAVWTUYDUVNUVPIVHVNUVIUVQIIUVDSXRVNUVE $.
      $( [12-Sep-2014] $)
$}

$( Infinite pigeonhole principle in its most general setting using cofinality. $)
${
    $d ph a x y z b c d e $.
    $d A x y z a b c d e $.
    $d B x y z a b c d e $.
    $d D y z a b c d e $.
    $d E x $.
    fiphp1d.1 $e |- ( ph -> A e. _V ) $.
    fiphp1d.2 $e |- ( ph -> Lim ( card ` A ) ) $.
    fiphp1d.3 $e |- ( ph -> B ~< ( cf ` ( card ` A ) ) ) $.
    fiphp1d.4 $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    fiphp1d.5 $e |- ( x = z -> D = E ) $.

    fiphp1d $p |- ( ph -> E. y e. B ( cf ` ( card ` A ) ) ~<_ { x e. A | D = y } ) $=
      ( cfv cv cdom wbr wceq wcel wa ccrd ccf cmpt ccnv cima wrex crab wlim csdm
      csn cvv wf eqid fmptd fiphp1 syl31anc wb wal simpr weq eleq1 anbi2d eleq1d
      wi imbi12d chvarv adantlr ax-17 adantl eqidd fvmptd syl3anc eqeq1d wfn ffn
      pm5.32da syl fniniseg sylan elrab a1i 3bitr4d alrimiv dfcleq sylibr breq2d
      biimpd reximdva mpd ) AEUANZUBNZBEGUCZUDCOZUJUEZPQZCFUFZWKGWMRZBEUGZPQZCFU
      FAEUKSWJUHFWKUIQEFWLULZWPIJKABEGFWLLWLUMUNZCEFWLUOUPAWOWSCFAWMFSZTZWOWSXCW
      NWRWKPXCDOZWNSZXDWRSZUQZDURWNWRRXCXGDXCXDESZXDWLNZWMRZTZXHHWMRZTZXEXFXCXHX
      JXLXCXHTZXIHWMXNXHXHHFSZXIHRXCXHUSZXPAXHXOXBABOZESZTZGFSZVDAXHTZXOVDBDBDUT
      ZXSYAXTXOYBXRXHAXQXDEVAVBYBGHFMVCVELVFVGXHBXDGHEWLFXHBVHYBGHRXHMVIXHWLVJVK
      VLVMVPAWLEVNZXBXEXKUQAWTYCXAEFWLVOVQEWMXDWLFVRVSXFXMUQXCWQXLBXDEYBGHWMMVMV
      TWAWBWCDWNWRWDWEWFWGWHWI $.
      $( [12-Sep-2014] $)
$}

${
    $d A x y z $.  $d ph x y z $.  $d B x y z $.  $d D y z $.  $d E x $.

    fiphp2d.1 $e |- ( ph -> A e. _V ) $.
    fiphp2d.2 $e |- ( ph -> Lim ( card ` A ) ) $.
    fiphp2d.3 $e |- ( ph -> ( cf ` ( card ` A ) ) = ( card ` A ) ) $.
    fiphp2d.4 $e |- ( ph -> B ~< A ) $.
    fiphp2d.5 $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    fiphp2d.6 $e |- ( x = z -> D = E ) $.

    fiphp2d $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ A ) $=
      ( cfv cdom wbr cvv wcel wa ccrd ccf cv wceq crab wrex cen csdm fvex cardcf
      a1i syl5req wb carden syl2anc mpbid jca sdomentr sylc fiphp1d wss ad2antrr
      ssrab2 ssdom2g ee10 endomtr sylancom sbth ex reximdva mpd ) AEUAOZUBOZGCUC
      ZUDZBEUEZPQZCFUFVPEUGQZCFUFABCDEFGHIJAVMRSZFEUHQZEVMUGQZTFVMUHQVSAVLUBUIUK
      ZAVTWALAVLVMUAOZUDZWAAWCVMVLVLUJKULAERSZVSWDWAUMIWBEVMRRUNUOUPZUQFEVMRURUS
      MNUTAVQVRCFAVNFSZTZVQVRWHVQTZVPEPQZEVPPQZVRWIWEVPEVAWJAWEWGVQIVBVOBEVCVPER
      VDVEWHVQWAWKAWAWGVQWFVBEVMVPVFVGVPEVHUOVIVJVK $.
      $( [12-Sep-2014] $)
$}

${
    $d A x y z $.  $d ph x y z $.  $d B x y z $.  $d D y z $.  $d E x $.
    fiphp3d.1 $e |- ( ph -> A ~~ NN ) $.
    fiphp3d.2 $e |- ( ph -> B e. Fin ) $.
    fiphp3d.3 $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    fiphp3d.4 $e |- ( x = z -> D = E ) $.

    fiphp3d $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN ) $=
      ( wceq cen wbr cn cvv wcel syl com crab wrex relen brrelexi ccrd cfv limom
      cv wlim wb omex jctir nnenom entr mpan2 carden biimprd sylc cardom syl6req
      limeq mpbii ccf cfom fveq2 eqeq12d csdm cfn ficard biimpd eleqtrd cardsdom
      wa id syl2anc mpbid fiphp2d simpr ad2antrr ex reximdva mpd ) AGCUHZMBEUAZE
      NOZCFUBWDPNOZCFUBABCDEFGHAEPNOZEQRZIEPNUCUDZSZAWGEUEUFZUIZIWGTUIZWLUGWGTWK
      MZWMWLUJWGWKTUEUFZTWGWHTQRZVMZETNOZWKWOMZWGWHWPWIUKULWGPTNOWRUMEPTUNUOWQWS
      WRETQQUPUQURUSUTZTWKVASVBSATVCUFZTMZWKVCUFZWKMZVDAWNXBXDUJAWGWNIWTSZWNXAXC
      TWKTWKVCVEWNVNVFSVBAFUEUFZWKRZFEVGOZAXFTWKAFVHRZXIXFTRZJJXIXIXJFVHVIVJURXE
      VKAXIWHXGXHUJJWJFEVHQVLVOVPKLVQAWEWFCFAWCFRZVMZWEWFXLWEVMWEWGWFXLWEVRAWGXK
      WEIVSWDEPUNVOVTWAWB $.
      $( [12-Sep-2014] $)

$}

${
    hashfz $p |- ( ( A e. ZZ /\ B e. ZZ /\ A <_ B ) -> ( # ` ( A ... B ) ) = ( ( B - A ) + 1 ) ) $=
      ( cz wcel cle wbr cfz co chash cfv c1 caddc wceq a1i syl2anc syl3anc wb cc
      cr cc0 w3a cmin cen simp1 simp2 1z zsubcl fzen cfn hashen mp2an sylibr zre
      fzfi 3ad2ant1 recnd 1re subcl addcom npcan eqtrd 3ad2ant2 addsub12 oveq12d
      zcn fveq2d cn0 peano2zdi 0reALT resubcl readdcl addid1 syl simp3 wa pncan3
      eqbrtrd eqcomd oveq2d breqtrd leadd2 mpbird nn0ge0i mpbii sylanbrc hashfz1
      1nn0 letrd elnn0z 3eqtrd ) ACDZBCDZABEFZUAZABGHZIJZAKAUBHZLHZBWQLHZGHZIJZK
      BAUBHZKLHZGHZIJZXCWNWOWTUCFZWPXAMZWNWKWLWQCDZXFWKWLWMUDZWKWLWMUEZWNKCDZWKX
      HXKWNUFNXIKAUGOWQABUHPWOUIDWTUIDXGXFQABUNWRWSUNWOWTUJUKULWNWTXDIWNWRKWSXCG
      WNWRWQALHZKWNARDZWQRDZWRXLMWNAWKWLASDZWMAUMUOZUPZWNKRDZXMXNWNKKSDZWNUQNZUP
      ZXQKAUROAWQUSOWNXRXMXLKMYAXQKAUTOVAWNWSKXBLHZXCWNBRDZXRXMWSYBMWLWKYCWMBVEV
      BZYAXQBKAVCPWNXRXBRDZYBXCMYAWNYCXMYEYDXQBAUROZKXBUSOVAVDVFWNXCVGDZXEXCMWNX
      CCDTXCEFYGWNXBWNWLWKXBCDXJXIBAUGOVHWNTXBTLHZXCTSDZWNVINZWNXBSDZYIYHSDZWNBS
      DZXOYKWLWKYMWMBUMVBXPBAVJOZYJXBTVKOZWNYKXSXCSDYNXTXBKVKOWNTYHEFZATLHZAYHLH
      ZEFZWNYQBYREWNYQABEWNXMYQAMXQAVLVMWKWLWMVNVQWNBAXBLHZYRWNXMYCBYTMXQYDXMYCV
      OYTBABVPVROWNXBYHALWNYHXBWNYEYHXBMYFXBVLVMVRVSVAVTWNYIYLXOYPYSQYJYOXPTYHAW
      APWBWNTKEFZYHXCEFZKWGWCWNYIXSYKUUAUUBQYJXTYNTKXBWAPWDWHXCWIWEXCWFVMWJ $.
      $( [12-Sep-2014] $)

    hashsdom $p |- ( ( A e. Fin /\ B e. Fin ) -> ( ( # ` A ) < ( # ` B ) <-> A ~< B ) ) $=
      ( cfn wcel wa chash cfv cle wbr wn cdom clt csdm wb ancoms cr hashcl nn0re
      cn0 3syl hashdom notbid simpl simpr ltnle syl2anc domtri con2bid 3bitr4d )
      ACDZBCDZEZBFGZAFGZHIZJZBAKIZJUNUMLIZABMIZULUOUQUKUJUOUQNBAUAOUBULUNPDZUMPD
      ZURUPNULUJUNSDUTUJUKUCAQUNRTULUKUMSDVAUJUKUDBQUMRTUNUMUEUFULUQUSUKUJUQUSJN
      BACCUGOUHUI $.
      $( [12-Sep-2014] $)

    fzsdom2 $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A <_ B -> ( B < C -> ( A ... B ) ~< ( A ... C ) ) ) ) $=
      ( cz wcel w3a cle wbr clt cfz co chash cfv cmin c1 cr zre 3ad2ant1 syl3anc
      wb csdm caddc simp3 3ad2ant2 3ad2ant3 ltsub1 mpbid resubcl syl2anc 1re a1i
      ltadd1 wceq simp11 simp12 simp2 hashfz simp13 wa ltle imp syl21anc 3brtr4d
      letrd cfn fzfi hashsdom mp2an sylib 3exp ) ADEZBDEZCDEZFZABGHZBCIHZABJKZAC
      JKZUAHZVNVOVPFZVQLMZVRLMZIHZVSVTBANKZOUBKZCANKZOUBKZWAWBIVTWDWFIHZWEWGIHZV
      TVPWHVNVOVPUCZVTBPEZCPEZAPEZVPWHTVNVOWKVPVLVKWKVMBQUDRZVNVOWLVPVMVKWLVLCQU
      ERZVNVOWMVPVKVLWMVMAQRRZBCAUFSUGVTWDPEZWFPEZOPEZWHWITVTWKWMWQWNWPBAUHUIVTW
      LWMWRWOWPCAUHUIWSVTUJUKWDWFOULSUGVTVKVLVOWAWEUMVKVLVMVOVPUNZVKVLVMVOVPUOVN
      VOVPUPZABUQSVTVKVMACGHWBWGUMWTVKVLVMVOVPURVTABCWPWNWOXAVTWKWLVPBCGHZWNWOWJ
      WKWLUSVPXBBCUTVAVBVDACUQSVCVQVEEVRVEEWCVSTABVFACVFVQVRVGVHVIVJ $.
      $( [12-Sep-2014] $)
$}

$( Lagrange's diophantine approximation theorem, lemma 62 in [vandenDries] $)

${
    $d x a b c $.  $d A a b c d x y z w $.  $d B a b c d x y z w $.
    irrapxlem1 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. ( 0 ... B ) ( x < y /\ ( |_ ` ( B x. ( ( A x. x ) mod 1 ) ) ) = ( |_ ` ( B x. ( ( A x. y ) mod 1 ) ) ) ) ) $=
        ? $.
    irrapxlem2 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. ( 0 ... B ) ( x < y /\ ( ( abs ` ( ( A x. x ) mod 1 ) - ( ( A x. y ) mod 1 ) ) < ( 1 / B ) ) ) ) $=
        ? $.
    irrapxlem3 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. NN0 ( abs ` ( ( A x. x ) - y ) ) < ( 1 / B ) ) $=
        ? $.

    irrapx1 $p |- ( A e. ( RR+ \ QQ ) -> { <. x , y >. | ( ( x e. NN /\ y e. NN ) /\ ( abs ` ( A - ( x / y ) ) ) e. ( 0 (,) ( 1 / ( y ^ 2 ) ) ) ) } ~~ NN ) $=
        ? $.
$}

$( ---- COMPUTABILITY ---- $)
$( Define Turing machines and computable functions and prove composition laws as needed. Polynomials are computable. $)

$( we're about to use this a ton, so give it a proper name $)

$c ,n 1st_n 2nd_n $.
${
    ccantor-pair $a class ,n $.
    ccantor-pair-1st $a class 1st_n $.
    ccantor-pair-2nd $a class 2nd_n $.
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

    nn0leadd2 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> A <_ ( A + B ) ) $=
      ( cn0 wcel wa cc0 caddc co cle cc wceq simpl addid1 3syl wbr nn0ge0 adantl
      nn0cn cr nn0re wb 0reALT a1i adantr leadd2 syl3anc mpbid eqbrtrrd ) ACDZBC
      DZEZAFGHZAABGHZIUKUIAJDULAKUIUJLARAMNUKFBIOZULUMIOZUJUNUIBPQUKFSDZBSDZASDZ
      UNUOUAUPUKUBUCUJUQUIBTQUIURUJATUDFBAUEUFUGUH $.
      $( [6-Sep-2014] $)

    nn0leadd1 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> B <_ ( A + B ) ) $=
      ( cn0 wcel wa cc0 caddc co cle cc wceq cr nn0re adantl recnd addid2 nn0ge0
      syl wbr adantr wb 0reALT a1i leadd1 syl3anc mpbid eqbrtrrd ) ACDZBCDZEZFBG
      HZBABGHZIUJBJDUKBKUJBUIBLDZUHBMNZOBPRUJFAISZUKULISZUHUOUIAQTUJFLDZALDZUMUO
      UPUAUQUJUBUCUHURUIAMTUNFABUDUEUFUG $.
      $( [6-Sep-2014] $)

    $( so we don't have to keep proving the same substitutions a billion times $)
    cantor-pair-lem13 $p |- ( A = B -> ( ( A x. ( A + 1 ) ) / 2 ) = ( ( B x. ( B + 1 ) ) / 2 ) ) $= ( wceq c1 caddc co cmul c2 cdiv id1 oveq1 oveq12d oveq1d ) ABCZAADEFZGFBBDEFZGFHINABOPGNJABDEKLM $.  $( [2-Sep-2014] $)
    cantor-pair-lem14 $p |- ( ( A = C /\ B = D ) -> ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) $= ( wceq wa caddc co c1 cmul c2 cdiv oveq12 cantor-pair-lem13 syl simpl oveq12d ) ACEZBDEZFZABGHZUAIGHJHKLHZCDGHZUCIGHJHKLHZACGTUAUCEUBUDEACBDGMUAUCNORSPQ $.  $( [2-Sep-2014] $)

    cantor-pair-value $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A ,n B ) = ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) ) $= ( va vb cn0 cv caddc co c1 cmul c2 cdiv ccantor-pair wceq weq mathbox cantor-pair-lem14 mpan2 eqid1 mpan df-cantor-pair ovex ovmpt2 ) CDABEECFZDFZGHZUFIGHJHKLHUDGHZABGHZUHIGHJHKLHZAGHZMAUEGHZUKIGHJHKLHAGHZUDANDDOUGULNDPUDUEAUEQRAANUEBNULUJNASAUEABQTCDUAUIAGUBUC $.  $( [2-Sep-2014] $)

    cantor-pair-lem3 $p |- ( A e. CC -> ( ( ( A + 1 ) x. ( ( A + 1 ) + 1 ) ) / 2 ) = ( ( ( A x. ( A + 1 ) ) / 2 ) + ( A + 1 ) ) ) $=
      ( cc wcel c1 caddc co cmul cdiv wceq ax-1cn ax-addass a1i syl3anc syl2anc
      c2 oveq2d oveq1d 3eqtrd ax-mulcl 2ne0 mp3an23 1p1e2apr1 peano2cn ax-distr
      eqtrd id1 2cn ax-mulcom cc0 wne wa jctir divdir divcan4 ) ABCZADEFZUPDEFZ
      GFZOHFAUPGFZUPOGFZEFZOHFZUSOHFZUTOHFZEFZVCUPEFUOURVAOHUOURUPAOEFZGFZUPAGF
      ZUTEFZVAUOUQVFUPGUOUQADDEFZEFZVFUODBCZVLUQVKIJJADDKUAUOVJOAEVJOIUOUBLPUEP
      UOUPBCZUOOBCZVGVIIAUCZUOUFZVNUOUGLZUPAOUDMUOVHUSUTEUOVMUOVHUSIVOVPUPAUHNQ
      RQUOUSBCZUTBCZVNOUIUJZUKVBVEIUOUOVMVRVPVOAUPSNUOVMVNVSVOVQUPOSNUOVNVTVQTU
      LUSUTOUMMUOVDUPVCEUOVMVNVTVDUPIVOVQVTUOTLUPOUNMPR $.
    $( [1-Sep-2014] $)
    cantor-pair-lem4 $p |- ( A = 0 -> ( ( A x. ( A + 1 ) ) / 2 ) = 0 ) $= ( cc0 wceq c1 caddc co cmul c2 cdiv oveq1 cc wcel id 0cnALT a1i eqeltrd ax-1cn ax-addcl syl2anc mul02 syl eqtrd oveq1d 2cn 2ne0 div0i syl6eq ) ABCZAADEFZGFZHIFBHIFBUHUJBHIUHUJBUIGFZBABUIGJUHUIKLZUKBCUHAKLDKLZULUHABKUHMBKLUHNOPUMUHQOADRSUITUAUBUCHUDUEUFUG $.  $( [1-Sep-2014] $)
    cantor-pair-lem5 $p |- ( A e. NN0 -> ( ( A x. ( A + 1 ) ) / 2 ) e. NN0 ) $=
      ( vb va cv c1 caddc co cmul c2 cdiv cn0 wcel cc0 cantor-pair-lem13 eleq1d
      wceq weq eqid1 cantor-pair-lem4 adantr ax-mp wa cc nn0cn cantor-pair-lem3
      0nn0 eqeltri syl simpr peano2nn0 nn0addcl syl2anc eqeltrd ex nn0ind ) BDZ
      UPEFGHGIJGZKLMMEFGHGIJGZKLCDZUSEFGZHGIJGZKLZUTUTEFGHGIJGZKLZAAEFGHGIJGZKL
      BCAUPMPUQURKUPMNOBCQUQVAKUPUSNOUPUTPUQVCKUPUTNOUPAPUQVEKUPANOURMKMMPURMPM
      RMSUAUFUGUSKLZVBVDVFVBUBZVCVAUTFGZKVFVCVHPZVBVFUSUCLVIUSUDUSUEUHTVGVBUTKL
      ZVHKLVFVBUIVFVJVBUSUJTVAUTUKULUMUNUO $.
    $( [1-Sep-2014] $)

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
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) < ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) $=
      ( cn0 wcel caddc co clt wbr c1 cmul c2 cdiv cr nn0re 3syl syl cc0 cle 1nn0
      wa w3a simp1 cantor-pair-lem9 nn0addcl sylancl cantor-pair-lem5 adantr 1re
      simp2 readdcl nn0leadd2 ltp1 lelttrd wb ltadd2 syl3anc mpbid cc wceq nn0cn
      cantor-pair-lem3 0re simp3 nn0ltp1le syl2anc cantor-pair-lem6 addid1 simpl
      breqtrrd nn0ge0 a1i 3jca leadd2 letrd ltletrd ) AEFZBEFZUBZCEFZDEFZUBZABGH
      ZCDGHZIJZUCZWDWDKGHZLHMNHZAGHZWHWHKGHLHMNHZWEWEKGHLHMNHZCGHZWGVTWJEFWJOFVT
      WCWFUDZABUEWJPQWGWHEFZWKEFWKOFWGVTWOWNVTWDEFZKEFWOABUFZUAWDKUFUGRZWHUHWKPQ
      ZWGWCWMEFWMOFVTWCWFUKZCDUEWMPQZWGVTWJWKIJWNVTWJWIWHGHZWKIVTAWHIJZWJXBIJZVT
      AWDWHVRAOFZVSAPUIZVTWPWDOFZWQWDPZRZVTXGKOFWHOFZXIUJWDKULUGZABUMVTWPXGWDWHI
      JWQXHWDUNQUOVTXEXJWIOFZXCXDUPXFXKVTWPWIEFXLWQWDUHWIPQAWHWIUQURUSVTWPWDUTFW
      KXBVAWQWDVBWDVCQVKRWGWKWLSGHZWMWSWGWLOFZSOFZXMOFWGWCXNWTWCWEEFZWLEFZXNCDUF
      ZWEUHZWLPQZRVDWLSULUGXAWGWKWLXMTWGWOXPWHWETJZWKWLTJWRWGWCXPWTXRRZWGWFYAVTW
      CWFVEWGWPXPWFYAUPWGVTWPWNWQRYBWDWEVFVGUSWHWEVHURWGWLUTFZXMWLVAWGXPXQYCYBXS
      WLVBQWLVIRVKWGSCTJZXMWMTJZWGWCWAYDWTWAWBVJCVLQWGWCXOCOFZXNUCYDYEUPWTWCXOYF
      XNXOWCVDVMWAYFWBCPUIXTVNSCWLVOQUSVPVQ $.

    $( first, use the trichotomy law to show that they must be in the same diagonal, because if > or < the values would be different.  then get the result by cancellation $)
    cantor-pair-lem8 $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 ) /\
        ( ( ( ( A + B ) x. ( ( A + B ) + 1 ) ) / 2 ) + A ) = ( ( ( ( C + D ) x. ( ( C + D ) + 1 ) ) / 2 ) + C ) ) -> ( A = C /\ B = D ) ) $=
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

    cantor-pair-lem10 $p |- E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = 0 $= ( cc0 cn0 wcel caddc co c1 cmul c2 cdiv wceq cv wrex 0nn0 cc ax-mp oveq1d oveq12d eqeq1d nn0addcli cantor-pair-lem5 nn0cn syl addid1i 00id cantor-pair-lem4 eqtri oveq1 id oveq2 rcla42ev mp3an ) CDEZUNCCFGZUOHFGZIGZJKGZCFGZCLZAMZBMZFGZVCHFGZIGZJKGZVAFGZCLZBDNADNOOUSURCURUODEZURPEZCCOOUAVIURDEVJUOUBURUCUDQUEUOCLURCLUFUOUGQUHVHUTCVBFGZVKHFGZIGZJKGZCFGZCLABCCDDVACLZVGVOCVPVFVNVACFVPVEVMJKVPVCVKVDVLIVACVBFUIZVPVCVKHFVQRSRVPUJSTVBCLZVOUSCVRVNURCFVRVMUQJKVRVKUOVLUPIVBCCFUKZVRVKUOHFVSRSRRTULUM $.  $( [1-Sep-2014] $)
    cantor-pair-lem11 $p |- ( A e. NN0 ->
        ( E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = A ->
            E. c e. NN0 E. d e. NN0 ( ( ( ( c + d ) x. ( ( c + d ) + 1 ) ) / 2 ) + c ) = ( A + 1 ) ) ) $=
      ( cn0 wcel caddc co c1 cmul c2 cdiv wceq cc0 adantr oveq1d ax-1cn syl3anc
      cc cv wrex wa wi w3a 0nn0 a1i simp3 simpl peano2nn0 simpl2 oveq2d 3ad2ant3
      3syl nn0cn 0cnALT addcom sylancl ax-addass 3eqtrd oveq12d cantor-pair-lem5
      0cn nn0addcl 1nn0 addid1 eqtr3d cantor-pair-lem3 adantl eqcomd eqtrd mpdan
      syl simpr oveq1 id eqeq1d oveq2 rcla42ev 3exp1 wn cn simp2 wo elnn0 biimpi
      cmin orcomd ord mpd nnm1nn0 subcl mpan2 sylancr weq eqid cantor-pair-lem14
      npcan mpan pm2.61d rexlimdvv ) AFGZBUAZCUAZHIZXEJHIZKIZLMIZXCHIZANZDUAZEUA
      ZHIZXMJHIZKIZLMIZXKHIZAJHIZNZEFUBDFUBZBCFFXBXDONZXCFGZXDFGZUCZXJXTUDUDXBYA
      YDXJXTXBYAYDUEZXJUCZOFGZXCJHIZFGZOYHHIZYJJHIZKIZLMIZOHIZXRNZXTYGYFUFUGYEYI
      XJYEYDYBYIXBYAYDUHYBYCUIZXCUJZUNPYFYNXFXFJHIZKIZLMIZXHXFHIZXRYFYTOHIZYNYTY
      FYTYMOHYFYSYLLMYFXFYJYRYKKYFXFXCOHIZJHIZOXCHIZJHIZYJYFXEUUCJHYFXDOXCHXBYAY
      DXJUKULQZYFUUCUUEJHYFXCTGZOTGZUUCUUENZYEUUHXJYDXBUUHYAYBUUHYCXCUOPZUMZPZUP
      XCOUQZURQYFUUIUUHJTGZUUFYJNZUUIYFUPUGUUMUUOYFRUGZOXCJUSZSUTYFXFYJJHYFXFUUD
      UUFYJUUGYFUUCUUEJHYFUUHUUIUUJUUMVCUUNURQYFUUIUUHUUOUUPUUIYFVCUGUUMUUQUURSU
      TQVAQQYFYTFGZYTTGUUBYTNYFXFFGZUUSYFXEFGZJFGUUTYEUVAXJYDXBUVAYAXCXDVDZUMZPZ
      VEXEJVDURXFVBVMYTUOYTVFUNVGYFUVAXETGZYTUUANUVDXEUOZXEVHUNYFUUAXIJHIZXRYEUU
      AUVGNZXJYEUVAUVHUVCYEUVAUCZUUAXHXEHIZJHIZUVGUVIXHTGZUVEUUOUUAUVKNUVIXHFGZU
      VLUVAUVMYEXEVBZVIXHUOZVMUVAUVEYEUVFVIUUOUVIRUGUVLUVEUUOUEUVKUUAXHXEJUSVJSU
      VIUVJXIJHUVIXEXCXHHUVIXEUUCXCUVIXDOXCHXBYAYDUVAUKULUVIUUHUUCXCNYEUUHUVAUUL
      PXCVFVMVKULQVKVLPYFXIAJHYEXJVNQVKUTXSYOOXLHIZUVPJHIZKIZLMIZOHIZXRNDEOYHFFX
      KONZXQUVTXRUWAXPUVSXKOHUWAXOUVRLMUWAXMUVPXNUVQKXKOXLHVOZUWAXMUVPJHUWBQVAQU
      WAVPVAVQXLYHNZUVTYNXRUWCUVSYMOHUWCUVRYLLMUWCUVPYJUVQYKKXLYHOHVRZUWCUVPYJJH
      UWDQVAQQVQVSSVTXBYAWAZYDXJXTXBUWEYDUEZXJUCZYIXDJWGIZFGZYHUWHHIZUWJJHIZKIZL
      MIZYHHIZXRNZXTUWFYIXJUWFYDYBYIXBUWEYDUHZYPYQUNPUWFUWIXJUWFXDWBGZUWIUWFUWEU
      WQXBUWEYDWCUWFYAUWQUWFUWQYAYDXBUWQYAWDZUWEYCUWRYBYCUWRXDWEWFVIUMWHWIWJXDWK
      VMPUWGUWJXENZUWOUWFUWSXJYDXBUWSUWEYDUWJXCJUWHHIZHIZXEYDUUHUUOUWHTGZUWJUXAN
      UUKUUOYDRUGZYCUXBYBYCXDTGZUUOUXBXDUOZRXDJWLZURVIXCJUWHUSSYDUWTXDXCHYDUXDUW
      TXDNYCUXDYBUXEVIUXDUWTUWHJHIZXDUXDUUOUXBUWTUXGNRUXDUUOUXBRUXFWMJUWHUQWNUXD
      UUOUXGXDNRXDJWRWMVKVMULVKUMPUWGUWSUCZUWNXHYHHIZXRUXHUWMXHYHHUXHUWLXGLMUXHU
      WJXEUWKXFKUWGUWSVNZUXHUWJXEJHUXJQVAQQUWGUXIXRNUWSUWGUXIUVGXRUWGYDUXIUVGNZU
      WFYDXJUWPPYDUVLUUHUUOUXKYDUVAUVMUVLUVBUVNUVOUNUUKUXCUVLUUHUUOUEUVGUXIXHXCJ
      USVJSVMUWGXIAJHUWFXJVNQVKPVKVLXSUWOYHXLHIZUXLJHIKILMIYHHIZXRNDEYHUWHFFXKYH
      NZXQUXMXRUXNEEWOXQUXMNXLWPXKXLYHXLWQWMVQXLUWHNZUXMUWNXRYHYHNUXOUXMUWNNYHWP
      YHXLYHUWHWQWSVQVSSVTWTXA $.
    $( [1-Sep-2014] $)

    cantor-pair-lem12 $p |- ( A e. NN0 -> E. a e. NN0 E. b e. NN0 ( ( ( ( a + b ) x. ( ( a + b ) + 1 ) ) / 2 ) + a ) = A ) $=
      ( ve vf vc vd cv caddc co c1 cmul cdiv wceq cn0 wrex eqeq2 2rexbidv weq
      c2 cantor-pair-lem10 wcel cantor-pair-lem11 eqid cantor-pair-lem14 eqeq1d
      cc0 mpan2 mpan cbvrex2v biimpi syl6 nn0ind ) BHZCHZIJZUPKIJLJTMJUNIJZDHZN
      ZCOPBOPUQUGNZCOPBOPUQEHZNZCOPBOPZUQVAKIJZNZCOPBOPZUQANZCOPBOPDEAURUGNUSUT
      BCOOURUGUQQRDESUSVBBCOOURVAUQQRURVDNUSVEBCOOURVDUQQRURANUSVGBCOOURAUQQRBC
      UAVAOUBVCFHZGHZIJZVJKIJLJTMJVHIJZVDNZGOPFOPZVFVABCFGUCVMVFVLVEUNVIIJZVNKI
      JLJTMJUNIJZVDNFGBCOOFBSZVKVOVDVPGGSVKVONVIUDVHVIUNVIUEUHUFGCSZVOUQVDBBSVQ
      VOUQNUNUDUNVIUNUOUEUIUFUJUKULUM $.
    $( [1-Sep-2014] $)

    cantor-pair-map $p |- ,n : ( NN0 X. NN0 ) --> NN0 $= ( va vb cv caddc co c1 cmul c2 cdiv cn0 wcel wral cxp ccantor-pair wf cantor-pair-lem9 rgen2 df-cantor-pair fmpt2 mpbi ) ACZBCZDEZUCFDEGEHIEUADEZJKZBJLAJLJJMJNOUEABJJUAUBPQABJJUDJNABRST $.

    cantor-pair     $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. NN0 /\ D e. NN0 ) /\ ( A ,n B ) = ( C ,n D ) ) -> ( A = C /\ B = D ) ) $=
      ( cn0 wcel wa ccantor-pair co wceq w3a caddc c1 cmul c2 cantor-pair-value
      cdiv simp1 simp2 3ad2ant1 eqcomd 3ad2ant2 3eqtrd cantor-pair-lem8 syl3anc
      simp3 ) AEFBEFGZCEFDEFGZABHIZCDHIZJZKZUGUHABLIZUMMLINIOQIALIZCDLIZUOMLINI
      OQICLIZJACJBDJGUGUHUKRUGUHUKSULUNUIUJUPULUIUNUGUHUIUNJUKABPTUAUGUHUKUFUHU
      GUJUPJUKCDPUBUCABCDUDUE $.
    $( [1-Sep-2014] $)

    cantor-pair-1   $p |- ,n : ( NN0 X. NN0 ) -1-1-> NN0 $=
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

    cantor-pair-o   $p |- ,n : ( NN0 X. NN0 ) -onto-> NN0 $=
      ( vc vd va vb cn0 cxp ccantor-pair wfo wf wceq wrex wral dffo3 wcel caddc
      cv cfv co wa ad2antlr cantor-pair-map cmul cdiv cantor-pair-lem12 opelxpi
      c1 c2 cop cantor-pair-value df-ov a1i simpr 3eqtr3rd fveq2 eqeq2d rcla4ev
      syl2anc ex rexlimdvva mpd rgen mpbir2an ) EEFZEGHVCEGIAPZBPZGQZJZBVCKZAEL
      BAVCEGMUAVHAEVDENZCPZDPZORZVLUFORUBRUGUCRVJORZVDJZDEKCEKVHVDCDUDVIVNVHCDE
      EVIVJENVKENSZSZVNVHVPVNSZVJVKUHZVCNZVDVRGQZJZVHVOVSVIVNVJVKEEUETVQVJVKGRZ
      VMVTVDVOWBVMJVIVNVJVKUITWBVTJVQVJVKGUJUKVPVNULUMVGWABVRVCVEVRJVFVTVDVEVRG
      UNUOUPUQURUSUTVAVB $.

    cantor-pair-1o  $p |- ,n : ( NN0 X. NN0 ) -1-1-onto-> NN0 $= ( cn0 cxp ccantor-pair wf1o wf1 wfo df-f1o cantor-pair-1 cantor-pair-o mpbir2an ) AABZACDKACEKACFKACGHIJ $.  $( [1-Sep-2014] $)

    cantor-pair-lem19 $p |- ( A e. NN0 -> A <_ ( ( A x. ( A + 1 ) ) / 2 ) ) $=
      ( va vb cv c1 caddc co cmul c2 cdiv cle wbr wceq cantor-pair-lem13 breq12d
      cc0 id weq cn0 wcel eqid1 cantor-pair-lem4 ax-mp breqtrri cantor-pair-lem5
      nn0ge0i peano2nn0 nn0leadd1 syl2anc cc nn0cn cantor-pair-lem3 syl breqtrrd
      0nn0 a1d nn0ind ) BDZURUREFGHGIJGZKLPPPEFGHGIJGZKLCDZVAVAEFGZHGIJGZKLZVBVB
      VBEFGHGIJGZKLZAAAEFGHGIJGZKLBCAURPMZURPUSUTKVHQURPNOBCRZURVAUSVCKVIQURVANO
      URVBMZURVBUSVEKVJQURVBNOURAMZURAUSVGKVKQURANOPPUTKPUOUFPPMUTPMPUAPUBUCUDVA
      STZVFVDVLVBVCVBFGZVEKVLVCSTVBSTVBVMKLVAUEVAUGVCVBUHUIVLVAUJTVEVMMVAUKVAULU
      MUNUPUQ $.
      $( [6-Sep-2014] $)

    cantor-pair-lesum $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A + B ) <_ ( A ,n B ) ) $=
      ( cn0 wcel wa caddc co c1 cmul c2 cdiv ccantor-pair cle nn0addcl nn0re syl
      cr cantor-pair-lem5 3syl wbr nn0ssre cantor-pair-map fovcl sseldi eqeltrrd
      cantor-pair-value cantor-pair-lem19 simpl nn0leadd2 syl2anc letrd breqtrrd
      ) ACDZBCDZEZABFGZUPUPHFGIGJKGZAFGZABLGZMUOUPUQURUOUPCDZUPQDABNZUPOPUOUTUQC
      DZUQQDVAUPRZUQOSUOUSURQABUFZUOCQUSUAABCCCLUBUCUDUEUOUTUPUQMTVAUPUGPUOVBUMU
      QURMTUOUTVBVAVCPUMUNUHUQAUIUJUKVDUL $.
      $( [6-Sep-2014] $)

    cantor-pair-le1 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> A <_ ( A ,n B ) ) $=
      ( cn0 wcel wa caddc co ccantor-pair cr adantr nn0addcl syl cantor-pair-map
      nn0re fovcl nn0leadd2 cantor-pair-lesum letrd ) ACDZBCDZEZAABFGZABHGZSAIDT
      ANJUAUBCDUBIDABKUBNLUAUCCDUCIDABCCCHMOUCNLABPABQR $.
    $( [1-Sep-2014] $)


    cantor-pair-fixpoint $p |- ( 0 ,n 0 ) = 0 $= ( cc0 ccantor-pair co caddc c1 cmul c2 cdiv cn0 wcel wceq 0nn0 cantor-pair-value mp2an 00id cantor-pair-lem4 oveq1d ax-mp eqtri ) AABCZAADCZUAEDCFCGHCZADCZAAIJZUDTUCKLLAAMNUCUAAUAAKZUCUAKOUEUBAADUAPQROSS $.  $( [2-Sep-2014] $)

    cantor-pair-le2 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> B <_ ( A ,n B ) ) $=
      ( cn0 wcel wa caddc co ccantor-pair cr adantl nn0addcl syl cantor-pair-map
      nn0re fovcl nn0leadd1 cantor-pair-lesum letrd ) ACDZBCDZEZBABFGZABHGZTBIDS
      BNJUAUBCDUBIDABKUBNLUAUCCDUCIDABCCCHMOUCNLABPABQR $.
      $( [6-Sep-2014] $)

    df-cantor-pair-1st $a |- 1st_n = ( 1st o. `' ,n ) $.
    df-cantor-pair-2nd $a |- 2nd_n = ( 2nd o. `' ,n ) $.

    cantor-pair-lem16 $p |- `' ,n : NN0 --> ( NN0 X. NN0 ) $=
      ( cn0 cxp ccantor-pair wf1o ccnv wf cantor-pair-1o f1ocnv f1of mp2b ) AABZ
      ACDAKCEZDAKLFGKACHAKLIJ $.
      $( [6-Sep-2014] $)

    ${
        cantor-pair-lem17.0 $e |- E = ( A o. `' ,n ) $.
        cantor-pair-lem18 $p |- E = ( ( A |` ( NN0 X. NN0 ) ) o. `' ,n ) $=
          ( ccantor-pair ccnv ccom cn0 cxp cres crn wss wceq cdm cantor-pair-map
          fdmi dfdm4 eqtr3i eqimss2i cores ax-mp eqtr4i ) BADEZFZAGGHZIUBFZCUBJZ
          UDKUEUCLUDUFDMUDUFUDGDNODPQRAUBUDSTUA $.
          $( [6-Sep-2014] $)

        cantor-pair-lem17.1 $e |- ( ( B e. NN0 /\ C e. NN0 ) -> ( A ` <. B , C >. ) = D ) $.
        cantor-pair-lem17.2 $e |- A : _V -onto-> _V $.
        cantor-pair-lem17 $p |- ( ( B e. NN0 /\ C e. NN0 ) -> ( E ` ( B ,n C ) ) = D ) $=
          ( cn0 wcel wa ccantor-pair co cfv ccnv ccom eqcomi wceq cvv a1i fveq1i
          cop wfun cxp fofun ax-mp cantor-pair-lem16 cantor-pair-map fovcl fvco3
          wfo syl3anc df-ov fveq2i wf1o cantor-pair-1o dvhopcl f1ocnvfv1 sylancr
          wf syl5eq fveq2d 3eqtrd syl5eqr ) BIJCIJKZBCLMZENVFALOZPZNZDVFVHEEVHFQ
          UAVEVIVFVGNZANZBCUBZANDVEAUCZIIIUDZVGUTZVFIJVIVKRVMVESSAUKVMHSSAUEUFTV
          OVEUGTBCIIILUHUIIVNVFAVGUJULVEVJVLAVEVJVLLNZVGNZVLVFVPVGBCLUMUNVEVNILU
          OVLVNJVQVLRUPICIBUQVNIVLLURUSVAVBGVCVD $.
          $( [6-Sep-2014] $)
    $}

    ${
        cantor-pair-lem15.0 $e |- ( NN0 =/= (/) -> ( A |` ( NN0 X. NN0 ) ) : ( NN0 X. NN0 ) -onto-> NN0 ) $.
        cantor-pair-lem15.1 $e |- B = ( A o. `' ,n ) $.
        cantor-pair-lem15 $p |- B : NN0 -onto-> NN0 $=
          ( cn0 wfo cxp cres ccantor-pair ccnv ccom cc0 wcel 0nn0 mp2b wf1o wceq
          c0 wne ax-mp ne0i cantor-pair-1o f1ocnv f1ofo foco mp2an crn wss dfdm4
          wb cdm cantor-pair-map fdmi eqimssi eqsstr3i cores eqtr4i foeq1 mpbir
          ) EEBFZEEAEEGZHZIJZKZFZVAEVBFZEVAVCFZVELEMERSVFNELUACOVAEIPEVAVCPVGUBV
          AEIUCEVAVCUDOEVAEVBVCUEUFBVDQUTVEUJBAVCKZVDDVCUGZVAUHVDVHQVIIUKZVAIUIV
          JVAVAEIULUMUNUOAVCVAUPTUQEEBVDURTUS $.
          $( [6-Sep-2014] $)
    $}

    cantor-pair-1stfo $p |- 1st_n : NN0 -onto-> NN0 $=
      ( c1st ccantor-pair-1st cn0 fo1stres df-cantor-pair-1st cantor-pair-lem15
      ) ABCCDEF $.
      $( [6-Sep-2014] $)

    cantor-pair-2ndfo $p |- 2nd_n : NN0 -onto-> NN0 $=
      ( c2nd ccantor-pair-2nd cn0 fo2ndres df-cantor-pair-2nd cantor-pair-lem15
      ) ABCCDEF $.
      $( [6-Sep-2014] $)

    cantor-pair-1op $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( 1st_n ` ( A ,n B ) ) = A ) $=
      ( c1st ccantor-pair-1st df-cantor-pair-1st cn0 wcel cop wceq op1stg adantr
      cfv fo1st cantor-pair-lem17 ) CABADEAFGABHCLAIBFGABFJKMN $.
      $( [6-Sep-2014] $)

    cantor-pair-2op $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( 2nd_n ` ( A ,n B ) ) = B ) $=
      ( c2nd ccantor-pair-2nd df-cantor-pair-2nd op2ndg fo2nd cantor-pair-lem17
      cn0 ) CABBDEABIIFGH $.
      $( [6-Sep-2014] $)

    cantor-pair-p12 $p |- ( A e. NN0 -> ( ( 1st_n ` A ) ,n ( 2nd_n ` A ) ) = A ) $=
      ( va vb vc cn0 wcel cv ccantor-pair wceq ccantor-pair-1st ccantor-pair-2nd
      cfv cxp wrex co wfo cantor-pair-o wa fveq2 sylan9eq foelrn mpan cop biimpi
      elxp2 adantl simpll 3eqtr4d simplr cantor-pair-1op cantor-pair-2op oveq12d
      df-ov a1i simpl eqtr4d syl2anc ex rexlimdvva mpan9 rexlimiva syl ) AEFZABG
      ZHLZIZBEEMZNZAJLZAKLZHOZAIZVGEHPVCVHQBVGEAHUAUBVFVLBVGVDVGFZVDCGZDGZUCZIZD
      ENCENZVFVLVMVRCDVDEEUEUDVFVQVLCDEEVFVNEFVOEFRZRZVQVLVTVQRZAVNVOHOZIZVSVLWA
      VEVPHLZAWBVQVEWDIVTVDVPHSUFVFVSVQUGWBWDIWAVNVOHUMUNUHVFVSVQUIWCVSRZVKWBAWE
      VIVNVJVOHWCVSVIWBJLVNAWBJSVNVOUJTWCVSVJWBKLVOAWBKSVNVOUKTULWCVSUOUPUQURUSU
      TVAVB $.
      $( [6-Sep-2014] $)
$}

${
    $( Facts about map, fz, and mapfz: if you have to use elmap, your subproof should probably be moved here. $)

    $d a b c d e f g h i A $.
    $d a b c d e f g h i B $.
    $d a b c d e f g h i C $.
    $d a b c d e f g h i D $.
    $d a b c d e f g h i r $.
    $d a b c d e f g h i R $.
    $d a b c d e f g h i x $.
    $d a b c d e f g h i y $.


    $( could still stand to be shortened but at least it's highly reusable $)
    elfz-lastp $p |- ( ( A e. ZZ /\ B e. ( 1 ... ( A + 1 ) ) ) ->
        ( B = ( A + 1 ) \/ B e. ( 1 ... A ) ) ) $=
      ( cz wcel c1 co cfz wa wn cle wbr ad2antlr jca wb elfz syl3anc syl2anc zre
      cr 3ad2ant1 caddc wceq simpll elfzelz simplr elfzel1 peano2zdi mpbid simpr
      mtbid w3a simp2r clt simp2l simp3 pm3.2 adantr adantl ltnle mpbird zltp1le
      bnj2 peano2z syl letri3 ex orrd orcomd ) ACDZBEAEUAFZGFDZHZBEAGFDZBVJUBZVL
      VMVNVLVMIZVNVLVOHZVIBCDZHZEBJKZBVJJKZHZVSBAJKZHZIZVNVPVIVQVIVKVOUCZVKVQVIV
      OBEVJUDLZMVPVKWAVIVKVOUEVPVQECDZVJCDZVKWANWFVKWGVIVOBEVJUFLZVPAWEUGBEVJOPU
      HVPVMWCVLVOUIVPVQWGVIVMWCNWFWIWEBEAOPUJVRWAWDUKZVNVTVJBJKZHZWJVTWKVRVSVTWD
      ULWJABUMKZWKWJWMWBIZWJVSWDWNVRVSVTWDUNVRWAWDUOVSWBWCVSWBUPVBQWJASDZBSDZWMW
      NNVRWAWOWDVIWOVQARUQTVRWAWPWDVQWPVIBRURTZABUSQUTVRWAWMWKNWDABVATUHMWJWPVJS
      DZVNWLNWQVRWAWRWDVIWRVQVIWHWRAVCVJRVDUQTBVJVEQUTPVFVGVH $.
      $( [6-Sep-2014] $)

    elfz-induct $p |- ( A e. NN0 -> ( ( 1 ... A ) u. { ( A + 1 ) } ) =
        ( 1 ... ( A + 1 ) ) ) $=
      ( va cn0 wcel c1 cfz co caddc csn cun fzssp1 nn0p1nn cle wbr fznn id1 nnre
      cn cr syl leid mpbir2and snssd unssd cv wral wa wceq wo cz nn0z elfz-lastp
      sylan ssun2 elsn biimpri sseldi elun1 jaoi ralrimiva dfss3 sylibr eqssd
      wss ) ACDZEAFGZAEHGZIZJZEVGFGZVEVFVHVJEACKVEVGVJVEVGRDZVGVJDZALVKVLVKVGVGM
      NZVGVGOVKPVKVGSDVMVGQVGUATUBTUCUDVEBUEZVIDZBVJUFVJVIVDVEVOBVJVEVNVJDZUGVNV
      GUHZVNVFDZUIZVOVEAUJDVPVSAUKAVNULUMVQVOVRVQVHVIVNVHVFUNVNVHDVQBVGUOUPUQVNV
      FVHURUSTUTBVJVIVAVBVC $.
      $( [7-Sep-2014] $)

    $( Can remove the last element of a sequence $)
    ${
    mapfz-rmlast.1 $e |- C e. _V $.
    mapfz-rmlast $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) ->
        ( B |` ( 1 ... A ) ) e. ( C ^m (  1 ... A ) ) ) $=
      ( cn0 wcel c1 caddc co cfz cmap cres wf wi fzssp1 fssres expcom ovex elmap
      wss syl 3imtr4g imp ) AEFZBCGAGHIZJIZKIFZBGAJIZLZCUHKIFZUDUFCBMZUHCUIMZUGU
      JUDUHUFTZUKULNGAEOUKUMULUFCUHBPQUACUFBDGUEJRSCUHUIDGAJRSUBUC $.
      $( [6-Sep-2014] $)

    mapfzres $p |- ( ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) /\
        D e. ( C ^m ( 1 ... B ) ) ) ->
        ( D |` ( 1 ... A ) ) e. ( C ^m ( 1 ... A ) ) ) $=
      ( cn0 wcel cle wbr w3a c1 cfz co cmap wf cz nn0z adantr ovex elmap cres wa
      wss simpr cuz cfv 3ad2ant1 simpl3 eluz2 syl3anbrc fzss2 syl fssres syl2anc
      3ad2ant2 ex 3imtr4g imp ) AFGZBFGZABHIZJZDCKBLMZNMGZDKALMZUAZCVENMGZVBVCCD
      OZVECVFOZVDVGVBVHVIVBVHUBZVHVEVCUCZVIVBVHUDVJBAUEUFGZVKVJAPGZBPGZVAVLVBVMV
      HUSUTVMVAAQUGRVBVNVHUTUSVNVABQUORUSUTVAVHUHABUIUJAKBUKULVCCVEDUMUNUPCVCDEK
      BLSTCVEVFEKALSTUQUR $.
      $( [7-Sep-2014] $)

    mapfzconsex $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) /\ D e. C ) ->
        ( B u. { <. ( A + 1 ) , D >. } ) e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) $=
      ( cn0 wcel c1 cfz co cmap caddc csn cun wf wceq ovex elmap cvv a1i w3a cop
      cin c0 simp2 sylib wss eqid wb simp3 fsng syl2anc mpbiri fzp1disj 3ad2ant1
      snssd fss fun syl21anc elfz-induct unidm feq23d mpbid sylibr ) AFGZBCHAIJZ
      KJGZDCGZUAZHAHLJZIJZCBVJDUBMZNZOZVMCVKKJGVIVFVJMZNZCCNZVMOZVNVIVFCBOZVOCVL
      OZVFVOUCUDPZVRVIVGVSVEVGVHUECVFBEHAIQRUFVIVODMZVLOZWBCUGVTVIWCVLVLPZVLUHVI
      VJSGZVHWCWDUIWEVIAHLQTVEVGVHUJZVJDSCVLUKULUMVIDCWFUPVOWBCVLUQULVEVGWAVHHAF
      UNUOVFVOCCBVLURUSVIVPVQVKCVMVEVGVPVKPVHAUTUOVQCPVICVATVBVCCVKVMEHVJIQRVD
      $.
      $( [7-Sep-2014] $)

    mapfzrecons $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... ( A + 1 ) ) ) ) ->
        B = ( ( B |` ( 1 ... A ) ) u. { <. ( A + 1 ) , ( B ` ( A + 1 ) ) >.
        } ) ) $=
      ( c1 caddc co cfz cmap wcel cn0 wf cres cfv cop csn cun wceq ovex a1i snid
      elmap wfn ffn adantl fnresdm syl elfz-induct adantr eqcomd reseq2d resundi
      wa eqtr3d ssun2 sseldi eleqtrd fnressn syl2anc uneq2d 3eqtrd sylan2b ) BCE
      AEFGZHGZIGJAKJZVDCBLZBBEAHGZMZVCVCBNOPZQZRCVDBDEVCHSUBVEVFUMZBBVGVCPZQZMZV
      HBVLMZQZVJVKBVDMZBVNVKBVDUCZVQBRVFVRVEVDCBUDUEZVDBUFUGVKVDVMBVKVMVDVEVMVDR
      VFAUHUIZUJUKUNVNVPRVKBVGVLULTVKVOVIVHVKVRVCVDJVOVIRVSVKVCVMVDVKVLVMVCVLVGU
      OVCVLJVKVCAEFSUATUPVTUQVDVCBURUSUTVAVB $.
      $( [7-Sep-2014] $)

    $( TODO: make a range singleton extraction lemma and redo this on top of fvsnun[12] $)
    mapfzconsval $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) /\ D e. C ) ->
        ( E e. ( 1 ... ( A + 1 ) ) -> ( ( E e. ( 1 ... A ) /\ ( ( B u.
        { <. ( A + 1 ) , D >. } ) ` E ) = ( B ` E ) ) \/ ( E = ( A + 1 ) /\
        ( ( B u. { <. ( A + 1 ) , D >. } ) ` E ) = D ) ) ) ) $=
      ( c1 co wceq wcel cfz cfv wa c0 3ad2ant2 a1i eqtrd wn syl syl2anc cn0 cmap
      caddc w3a cop csn cun wo wi simp1 eqcomd wfun cdm wf ovex elmap ffun sylbi
      cin funsn simp22 biimpi fdm 3syl dmsnop ineq12d fzp1disj 3ad2ant1 syl21anc
      fvun cle wbr clt cr nn0re ltp1 peano2re ltnle mpbid intnand nn0z peano2zdi
      wb cz 1z elfz syl3anc mtbird eleq1d mtbid eleq2d ndmfv fveq2d simp23 fvsng
      cvv uneq12d 0ss ssid unssi ssun2 eqssi olcd 3exp elfz-lastp eqimss2 eqimss
      jca simp3 eqssd con3i adantr simpr ord mpd wne df-ne sylibr fvunsn pm2.61i
      orcd ) AGUCHZEIZAUAJZBCGAKHZUBHJZDCJZUDZEGYBKHJZEYEJZEBYBDUEUFZUGLZEBLZIZM
      ZEYBIZYLDIZMZUHZUIUIYCYHYIYSYCYHYIUDZYRYOYTYPYQYTYBEYCYHYIUJZUKZYTYLYMEYKL
      ZUGZDYTBULZYKULZBUMZYKUMZUSZNIYLUUDIYHYCUUEYIYFYDUUEYGYFYECBUNZUUECYEBFGAK
      UOUPZYECBUQUROOUUFYTYBDAGUCUOZUTPYTUUIYEYBUFZUSZNYTUUGYEUUHUUMYTYFUUJUUGYE
      IZYCYDYFYGYIVAYFUUJUUKVBYECBVCZVDUUHUUMIYTYBDVEPVFYHYCUUNNIZYIYDYFUUQYGGAU
      AVGVHOQEBYKVJVIYTUUDNDUGZDYTYMNUUCDYTEUUGJZRYMNIYTYJUUSYTYBYEJZYJYHYCUUTRZ
      YIYDYFUVAYGYDUUTGYBVKVLZYBAVKVLZMZYDUVCUVBYDAYBVMVLZUVCRZYDAVNJZUVEAVOZAVP
      SYDUVGYBVNJZUVEUVFWCUVHYDUVGUVIUVHAVQSAYBVRTVSVTYDYBWDJGWDJZAWDJZUUTUVDWCY
      DAAWAZWBUVJYDWEPUVLYBGAWFWGWHVHOYTYBEYEUUAWIWJYTYEUUGEYTUUGYEYHYCUUOYIYFYD
      UUOYGYFUUJUUOUUKUUPUROOUKWKWJEBWLSYTUUCYBYKLZDYTEYBYKUUBWMYTYBWPJZYGUVMDIU
      VNYTUULPYCYDYFYGYIWNYBDWPCWOTQWQUURDIYTUURDNDDDWRDWSWTDNXAXBPQQXHXCXDYCRZY
      HYIYSUVOYHYIUDZYOYRUVPYJYNUVPUVOYPYJUHZYJUVOYHYIUJZUVPUVKYIUVQYHUVOUVKYIYD
      YFUVKYGUVLVHOUVOYHYIXIAEXETUVOUVQMZYPRZYJUVOUVTUVQYPYCYPYBEYBEXFEYBXGXJXKX
      LUVSYPYJUVOUVQXMXNXOTUVPYBEXPZYNUVPUVOUWAUVRYBEXQXRBYBDEXSSXHYAXDXT $.
      $( [7-Sep-2014] $)

    ${
    $d c d e f g h i j ph $.
    mapfzinde.10 $e |- [ 0 / a ] [ (/) / b ] ph $.
    mapfzinde.11 $e |- ( ( c e. NN0 /\ d e. ( C ^m ( 1 ... c ) ) /\ e e. C ) -> ( [ c / a ] [ d / b ] ph -> [ ( c + 1 ) / a ] [ ( d u. { <. ( c + 1 ) , e >. } ) / b ] ph ) ) $.

    mapfzinde.base $p |- A. f e. ( C ^m ( 1 ... 0 ) ) [ 0 / a ] [ f / b ] ph $=
      ( cc0 wsbc co cmap wcel c0 wceq cvv c1o wsb c1 cfz cv fz10OLD oveq2i map0e
      wb eqtri eleq2i biimpi el1o eqimss2 eqimss eqssd 3syl cc 0cn elexi sbcbidv
      dfsbcq sylancl mpbii rgen ) AFDUAZELMZDBUBLUCNZONZDUDZVHPZAFQMZELMZVFJVJQV
      IRZLSPVLVFUHVJVITPZVIQRZVMVJVNVHTVIVHBQONTVGQBOUEUFBIUGUIUJUKVNVOVIULUKVOQ
      VIQVIUMVIQUNUOUPLUQURUSVMVKVEELSAFQVIVAUTVBVCVD $.
      $( [7-Sep-2014] $)

    mapfzinde.ind $p |- ( g e. NN0 -> ( A. f e. ( C ^m ( 1 ... g ) ) [ g / a ]
        [ f / b ] ph -> A. f e. ( C ^m ( 1 ... ( g + 1 ) ) ) [ ( g + 1 ) / a ]
        [ f / b ] ph ) ) $=
      ( vh wcel wsb c1 co wsbc wa wb cv cn0 cmap wral caddc mapfz-rmlast adantlr
      cfz cres simplr wceq cvv vex sbcbidv mpan2 rcla4va syl2anc cfv cop csn cun
      dfsbcq simplll jca wf ovex elmap biimpi cn cle nn0p1nn nn0re peano2re leid
      wbr cr 3syl fznn syl mpbird ffvelrn syl2anr anim1i resexOLD fvex weq simp1
      w3a eleq1d simp2 oveq2d eleq12d anbi12d simp3 3ad2ant1 bitrd oveq1 opeq12d
      wi oveq1d sneqd uneq12d imbi12d simpll simprl 3jca simprr sylc mapfzrecons
      vtocl3 mpdan ralrimiva cbvralv sylib ex ) EUAZUBNZAGDOZFEOZDBPXPUHQZUCQZUD
      ZXRFXPPUEQZRZDBPYCUHQZUCQZUDZXQYBSZAGMOZFYCRZMYFUDYGYHYJMYFYHMUAZYFNZSZAGY
      KXTUIZRZFEOZYJYMYNYANZYBYPXQYLYQYBXPYKBJUFZUGXQYBYLUJXSYPDYNYADUAZYNUKZXPU
      LNZXSYPTEUMZYTXRYOFXPULAGYSYNVBUNUOUPUQYMYPSZYJAGYNYCYCYKURZUSZUTZVAZRZFYC
      RZUUCXQYQSZUUDBNZYPSZUUIUUCXQYQXQYBYLYPVCZUUCXQYLYQUUMYHYLYPUJZYRUQVDYMUUK
      YPXQYLUUKYBYLYEBYKVEZYCYENZUUKXQYLUUOBYEYKJPYCUHVFVGVHXQUUPYCVINZYCYCVJVOZ
      SZXQUUQUURXPVKZXQXPVPNYCVPNUURXPVLXPVMYCVNVQVDXQUUQUUPUUSTUUTYCYCVRVSVTYEB
      YCYKWAWBUGWCHUAZUBNZIUAZBPUVAUHQZUCQZNZSZCUAZBNZAGIOZFHOZSZSZAGUVCUVAPUEQZ
      UVHUSZUTZVAZRZFUVNRZWSUUJUULSZUUIWSHICXPYNUUDUUBYKXTMUMWDYCYKWEHEWFZUVCYNU
      KZUVHUUDUKZWHZUVMUVTUVSUUIUWDUVGUUJUVLUULUWDUVBXQUVFYQUWDUVAXPUBUWAUWBUWCW
      GZWIUWDUVCYNUVEYAUWAUWBUWCWJZUWDUVDXTBUCUWDUVAXPPUHUWEWKWKWLWMUWDUVIUUKUVK
      YPUWDUVHUUDBUWAUWBUWCWNZWIUWDUVKUVJFEOZYPUWAUWBUVKUWHTUWCUVJFUVAXPVBWOUWDU
      UAUWHYPTUUBUWDUVJYOFXPULUWDUWBUVJYOTUWFAGUVCYNVBVSUNUOWPWMWMUWDUVSUVRFYCRZ
      UUIUWDUVNYCUKZUVSUWITUWAUWBUWJUWCUVAXPPUEWQWOUVRFUVNYCVBVSUWDYCULNZUWIUUIT
      XPPUEVFZUWDUVRUUHFYCULUWDUVQUUGUKUVRUUHTUWDUVCYNUVPUUFUWFUWDUVOUUEUWDUVNYC
      UVHUUDUWDUVAXPPUEUWEWTUWGWRXAXBAGUVQUUGVBVSUNUOWPXCUVMUVBUVFUVIWHUVKUVSUVM
      UVBUVFUVIUVBUVFUVLXDUVBUVFUVLUJUVGUVIUVKXEXFUVGUVIUVKXGLXHXJUQUUCXQYLYJUUI
      TZUUMUUNXQYLSZUWKUWMUWLUWNYIUUHFYCULUWNYKUUGUKYIUUHTXPYKBJXIAGYKUUGVBVSUNU
      OUQVTXKXLYJYDMDYFMDWFZUWKYJYDTUWLUWOYIXRFYCULAGYKYSVBUNUOXMXNXO $.
      $( [7-Sep-2014] $)

    mapfzinde $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> [ A / a ] [ B / b ] ph ) $=
      ( vh vg c1 cfz co cmap wsbc wral vf cn0 wcel wa wsb caddc wceq eqidd oveq2
      cc0 dfsbcq raleqbidv weq oveq2d mapfzinde.base mapfzinde.ind nn0ind adantr
      cv oveq123d simpll simplr jca simpr simpl sbcbidv syl2anc rcla4dv imp mpd
      wb ex ) BUBUCZCDOBPQZRQZUCZUDZAGMUEZFBSZMVOTZAGCSZFBSZVMVTVPVRFUAUEZMDOUAU
      SZPQZRQZTVRFUJSZMDOUJPQZRQZTVRFNUEZMDONUSZPQZRQZTVRFWKOUFQZSZMDOWNPQZRQZTV
      TUANBWDUJUGZWCWGMWFWIWRDDWEWHRRWRRUHWRDUHWDUJOPUIUTVRFWDUJUKULUANUMZWCWJMW
      FWMWSDDWEWLRRWSRUHWSDUHWDWKOPUIUTVRFWDWKUKULWDWNUGZWCWOMWFWQWTWEWPDRWDWNOP
      UIUNVRFWDWNUKULWDBUGZWCVSMWFVOXAWEVNDRWDBOPUIUNVRFWDBUKULADEMFGHIJKLUOADEM
      NFGHIJKLUPUQURVQVTWBVQVTUDZVQVTWBXBVMVPVMVPVTVAVMVPVTVBVCVQVTVDVQVTWBVMVSW
      BMCVOVMMUSZCUGZUDXDVMVSWBVKVMXDVDVMXDVEXDVRWAFBUBAGXCCUKVFVGVHVIVGVLVJ $.
      $( [7-Sep-2014] $)
    $}

    ${
    $d f g h i   a b c d e A $.
    $d f g h i   a b c d e B $.
    $d f g h i   c d e ph $.
    $d f g h i   a b ps $.
    $d f g h i   a b ch $.
    $d f g h i   a b th $.
    $d f g h i   a b ta $.

    mapfzind.2 $e |- ( ( a = A /\ b = B )   -> ( ph <-> ps ) ) $.
    mapfzind.4 $e |- ( ( a = 0 /\ b = (/) ) -> ( ph <-> ch ) ) $.
    mapfzind.6 $e |- ( ( a = c /\ b = d )   -> ( ph <-> th ) ) $.
    mapfzind.8 $e |- ( ( a = ( c + 1 ) /\ b = ( d u. { <. ( c + 1 ) , e >.
        } ) ) -> ( ph <-> ta ) ) $.
    mapfzind.10 $e |- ch $.
    mapfzind.11 $e |- ( ( c e. NN0 /\ d e. ( C ^m ( 1 ... c ) ) /\ e e. C ) -> ( th -> ta ) ) $.

    mapfzind $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> ps ) $=
      ( cn0 wcel c1 cfz co cmap wa wsbc c0 cc0 cc 0cn elexi 0ex sbc2ie mpbir w3a
      cv wsb caddc cop csn cun vex ovex snex unex mapfzinde ax-17 sbc2iegf mpbid
      3imtr4g ) FUAUBGHUCFUDUEUFUEZUBZUGAKGUHJFUHBAFGHIJKLMNAKUIUHJUJUHCSACJKUJU
      IUJUKULUMUNPUOUPLURZUAUBMURZHUCVOUDUEUFUEUBIURZHUBUQDEAKMUSJLUSAKVPVOUCUTU
      EZVQVAZVBZVCZUHJVRUHTADJKVOVPLVDMVDZQUOAEJKVRWAVOUCUTVEVPVTWBVSVFVGRUOVLVH
      ABJKFGUAVMBJVIBKVIVNJVIOVJVK $.
      $( [7-Sep-2014] $)
    $}

    mapssi $p |- ( ( A C_ B /\ B e. _V ) -> ( A ^m C ) C_ ( B ^m C ) ) $=
      ( va cvv wcel wss cmap co wa cv wf cab wi fss wceq ancoms mapvalg sylancl
      expcom adantl ss2abdv ssexg simpl 3sstr4d ) BFGZABHZACIJZBCIJZHUGUHKZCAELZ
      MZENZCBULMZENZUIUJUKUMUOEUHUMUOOUGUMUHUOCABULPUAUBUCUKAFGZCFGZUIUNQUHUGUQA
      BFUDRDACFFESTUKUGURUJUPQUGUHUEDBCFFESTUFR $.
      $( [6-Sep-2014] $)
    $}

    ${
        mapcan0.0 $e |- B e. _V $.
        mapcan0.1 $e |- C e. _V $.
        mapcan0.2 $e |- D e. _V $.
        mapcan0.3 $e |- E e. _V $.

        mapcan0 $p |- ( ( A e. ( B ^m C ) /\ A e. ( D ^m E ) ) -> C = E ) $=
          ( cmap co wcel wa cdm wceq wf elmap biimpi fdm syl adantr adantl
          eqtr3d ) ABCJKLZADEJKLZMANZCEUDUFCOZUEUDCBAPZUGUDUHBCAFGQRCBASTUAUEUFE
          OZUDUEEDAPZUIUEUJDEAHIQREDASTUBUC $.
          $( [4-Sep-2014] $)
    $}

    ${
        constmap.1 $e |- A e. _V $.
        constmap.2 $e |- B e. _V $.
        constmap.3 $e |- C e. _V $.
        $( a constant is a function $)
        constmap $p |- ( B e. C -> ( A X. { B } ) e. ( C ^m A ) )  $= ( wcel csn cmap co cxp wss snssi mapss syl wf fconst snex elmap mpbir a1i sseldd ) BCGZBHZAIJZCAIJZAUDKZUCUDCLUEUFLBCMUDCAFDNOUGUEGZUCUHAUDUGPABEQUDAUGBRDSTUAUB $.  $( [30-Aug-2014] $)
    $}

    ${
        mapcan1.0 $e |- A e. B $.
        mapcan1.1 $e |- C e. _V $.
        mapcan1.2 $e |- D e. _V $.
        mapcan1.3 $e |- B e. _V $.

        mapcan1 $p |- ( ( B ^m C ) = ( B ^m D ) -> C = D ) $=
          ( csn cxp cmap co wcel wceq elexi constmap ax-mp wa simpl simpr syldan
          eleqtrd mapcan0 mpan ) CAIJZBCKLZMZUFBDKLZNZCDNZABMUGECABFABEOHPQUGUIU
          EUHMUJUGUIRUEUFUHUGUISUGUITUBUEBCBDHFHGUCUAUD $.
          $( [4-Sep-2014] $)
    $}

    ${
    mapco1.1 $e |- C e. _V $.
    mapco1.2 $e |- A e. _V $.
    ${
    mapco1.3 $e |- E e. _V $.
    mapco1 $p |- ( ( B e. ( C ^m A ) /\ D : C --> E ) ->
        ( D o. B ) e. ( E ^m A ) ) $=
      ( cmap co wcel wf wa ccom simpr elmap biimpi adantr fco syl2anc sylibr ) B
      CAIJKZCEDLZMZAEDBNZLZUEEAIJKUDUCACBLZUFUBUCOUBUGUCUBUGCABFGPQRACEDBSTEAUEH
      GPUA $.
      $( [7-Sep-2014] $)
    $}
    mapfun $p |- ( B e. ( A ^m C ) -> Fun B ) $=
      ( cmap co wcel wf wfun elmap ffun sylbi ) BACFGHCABIBJACBEDKCABLM $.
      $( [7-Sep-2014] $)
    elmapdm $p |- ( B e. ( A ^m C ) -> dom B = C ) $=
      ( cmap co wcel wf cdm wceq elmap fdm sylbi ) BACFGHCABIBJCKACBEDLCABMN $.
      $( [7-Sep-2014] $)
    mapfv $p |- ( ( B e. ( A ^m C ) /\ D e. C ) -> ( B ` D ) e. A ) $=
      ( cmap co wcel wf cfv elmap ffvelrn sylanb ) BACGHICABJDCIDBKAIACBFELCADBM
      N $.
      $( [7-Sep-2014] $)
    ${
    $d u B $. $d u C $. $d u D $.
    mapdmres.3 $e |- D e. _V $.
    mapdmres $p |- ( ( B e. ( A ^m C ) /\ A. u e. C ( B ` u ) e. D ) ->
        B e. ( D ^m C ) ) $=
      ( cmap co wcel cv cfv wral wa wf wfn crn wss elmap ffn sylbi fnfvrnss df-f
      adantr sylan sylanbrc sylibr ) CBDIJKZALCMEKADNZOZDECPZCEDIJKUKCDQZCRESZUL
      UIUMUJUIDBCPUMBDCGFTDBCUAUBZUEUIUMUJUNUOADECUCUFDECUDUGEDCHFTUH $.
      $( [7-Sep-2014] $)
    $}
    $}

    ${
    elmapfz.0 $e |- C e. _V $.
    elmapfz0 $p |- (/) e. ( C ^m ( 1 ... 0 ) ) $=
      ( c0 c1o c1 cc0 cfz co cmap 0lt1o fz10 oveq2i map0e eqtri eleqtrri ) CDAEF
      GHZIHZJQACIHDPCAIKLABMNO $.
      $( [9-Sep-2014] $)
    elmapfz1 $p |- ( A e. C -> { <. 1 , A >. } e. ( C ^m ( 1 ... 1 ) ) ) $=
      ( wcel c1 cfz co cop csn wf cmap wss cz wa wceq jctl eqidd syl2anc sylibr
      1z fsng biimpar snssiALT fss fzsn ax-mp feq2i ovex elmap ) ABDZEEFGZBEAHIZ
      JZULBUKKGDUJEIZBULJZUMUJUNAIZULJZUPBLUOUJEMDZUJNZULULOZUQUJURTPUJULQUSUQUT
      EAMBULUAUBRABUCUNUPBULUDRUKUNBULURUKUNOTEUEUFUGSBUKULCEEFUHUIS $.
      $( [9-Sep-2014] $)
    elmapfz2 $p |- ( ( A e. C /\ B e. C ) -> { <. 1 , A >. , <. 2 , B >. } e. ( C ^m ( 1 ... 2 ) ) ) $=
      ( wcel wa c1 c2 cpr cop wf cfz co cmap wss cn0 wne 1nn0 2nn0 pm3.2i oveq2i
      1ne2 fprg mp3an13 prssg ibi fss syl2anc ovex elmap caddc df-2 cz wceq fzpr
      1z ax-mp 1p1e2apr1 preq2i 3eqtri feq2i bitri sylibr ) ACEBCEFZGHIZCGAJHBJI
      ZKZVFCGHLMZNMEZVDVEABIZVFKZVJCOZVGGPEZHPEZFVDGHQVKVMVNRSTUBGHABPPCCUCUDVDV
      LABCCCUEUFVEVJCVFUGUHVIVHCVFKVGCVHVFDGHLUIUJVHVECVFVHGGGUKMZLMZGVOIZVEHVOG
      LULUAGUMEVPVQUNUPGUOUQVOHGURUSUTVAVBVC $.
      $( [9-Sep-2014] $)
    ${
    $d x C $.
    elmapeliunmap $p |- ( ( A e. NN0 /\ B e. ( C ^m ( 1 ... A ) ) ) -> B e. U_ x e. NN0 ( C ^m ( 1 ... x ) ) ) $=
      ( va cn0 wcel c1 cfz co cmap wa cv ciun wrex wceq oveq2 oveq2d eleq2d weq
      rcla4ev eliun sylibr cbviunv syl6eleq ) BGHCDIBJKZLKZHZMZCFGDIFNZJKZLKZOZA
      GDIANZJKZLKZOUJCUMHZFGPCUNHURUIFBGUKBQZUMUHCUSULUGDLUKBIJRSTUBFCGUMUCUDFAG
      UMUQFAUAULUPDLUKUOIJRSUEUF $.
      $( [9-Sep-2014] $)
    $}
    $}
$}

$( Note for future: a-i are dummy variables that are disjoint from each other
   and from all other variables.  they should not be used in the statement of
   a theorem. $)

$c FRSD FRSDrank FRSDlevel $.
cfrsd $a class FRSD $.
cfrsdrank $a class FRSDrank $.
cfrsdlevel $a class FRSDlevel $.
${
    $( Finite-recursive set descriptions / Inductive ADTs for combinatorial objects $)

    $d a b c d e f g h i A $.
    $d a b c d e f g h i B $.
    $d a b c d e f g h i C $.
    $d a b c d e f g h i D $.
    $d a b c d e f g h i r $.
    $d a b c d e f g h i u $.
    $d a b c d e f g h i v $.
    $d a b c d e f g h i w $.
    $d a b c d e f g h i x $.
    $d a b c d e f g h i y $.
    $d a b c d e f g h i z $.
    $d a b c d e f g h i R $.

    $( FRSD defines a set as the closure of a defining relation composed with
       the taking of finite sequences.  If infinite sequences were allowed, we
       could not guarantee a fixed point at ` om ` . $)
    ${
    $d x y z $.
    df-frsd $a |- FRSD = ( x e. _V |-> ( rec ( ( y e. _V |->
        ( x " U_ z e. NN0 ( y ^m ( 1 ... z ) ) ) ) , (/) ) ` om ) ) $.

    df-frsdlevel $a |- FRSDlevel = ( x e. _V |-> ( rec ( ( y e. _V |->
        ( x " U_ z e. NN0 ( y ^m ( 1 ... z ) ) ) ) , (/) ) |` om ) ) $.

    df-frsdrank $a |- FRSDrank = ( x e. _V |-> ( y e. ( FRSD ` x ) |->
        |^| { z e. om | y e. ( ( FRSDlevel ` x ) ` z ) } ) ) $.
    $}

    $( Substitution lemma for FRSD $)
    frsd-lem1 $p |- ( R e. _V -> ( FRSD ` R ) = ( rec ( ( a e. _V |->
        ( R " U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) , (/) ) ` om ) ) $=
      ( vc com cvv cv cn0 c1 cfz co cmap ciun cima cmpt c0 crdg cfv cfrsd wceq
      wcel imaeq1 adantr mpteq2dva rdgeq1 syl fveq1d df-frsd fvex fvmpt ) DAEBFD
      GZCHBGZICGJKLKMZNZOZPQZREBFAUMNZOZPQZRFSUKATZEUPUSUTUOURTUPUSTUTBFUNUQUTUN
      UQTULFUAUKAUMUBUCUDPUOURUEUFUGDBCUHEUSUIUJ $.
      $( [6-Sep-2014] $)

    frsd-lem9 $p |- ( a e. _V |-> ( R " U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) =
        ( c e. _V |-> ( R " U_ d e. NN0 ( c ^m ( 1 ... d ) ) ) ) $=
      ( cvv cn0 cv c1 cfz co cmap ciun cima weq wceq wcel oveq1 adantr iuneq2dv
      oveq2 oveq2d cbviunv syl6eq imaeq2d cbvmptv ) BDFACGBHZICHZJKZLKZMZNAEGDHZ
      IEHZJKZLKZMZNBDOZUKUPAUQUKCGULUILKZMUPUQCGUJURUQUJURPUHGQUGULUILRSTCEGURUO
      CEOUIUNULLUHUMIJUAUBUCUDUEUF $.
      $( [7-Sep-2014] $)

    ${
    $d x y R $.
    $d x y A $.
    frsd-lem13.1 $e |- R e. _V $.
    frsd-lem13 $p |- ( FRSDlevel ` R ) = ( rec ( ( x e. _V |->
        ( R " U_ y e. NN0 ( x ^m ( 1 ... y ) ) ) ) , (/) ) |` om ) $=
      ( va cvv wcel cfrsdlevel cfv cv co cima cmpt crdg com cres wceq con0 ax-mp
      c0 cn0 c1 cfz cmap ciun imaeq1 adantr mpteq2dva rdgeq1 reseq1 df-frsdlevel
      3syl wfun wfn rdgfnon fnfun omex resfunexg mp2an fvmpt ) CFGCHIAFCBUAAJZUB
      BJUCKUDKUEZLZMZTNZOPZQDECAFEJZVBLZMZTNZOPZVFFHVGCQZVIVDQVJVEQVKVFQVLAFVHVC
      VLVHVCQVAFGVGCVBUFUGUHTVIVDUIVJVEOUJULEABUKVEUMZOFGVFFGVERUNVMTVDUORVEUPSU
      QVEOFURUSUTS $.
      $( [7-Sep-2014] $)

    frsd-lem15 $p |- ( FRSDrank ` R ) = ( y e. ( FRSD ` R ) |->
        |^| { x e. om | y e.  ( ( FRSDlevel ` R ) ` x ) } ) $=
      ( va cvv wcel cfrsdrank cfv cfrsd cfrsdlevel com crab cint cmpt wceq fveq2
      cv fveq1d eleq2d rabbidv inteqd mpteq12dv df-frsdrank mptex fvmpt ax-mp
      fvex ) CFGCHIBCJIZBRZARZCKIZIZGZALMZNZOZPDECBERZJIZUJUKURKIZIZGZALMZNZOUQF
      HURCPZBUSVDUIUPURCJQVEVCUOVEVBUNALVEVAUMUJVEUKUTULURCKQSTUAUBUCEBAUDBUIUPC
      JUHUEUFUG $.
      $( [7-Sep-2014] $)

    frsd-lem17 $p |- ( FRSD ` R ) = U_ x e. om ( ( FRSDlevel ` R ) ` x ) $=
      ( va vb com cvv cn0 cv c1 cfz co cmap ciun cima cmpt c0 cfv wcel wceq crdg
      cfrsd cfrsdlevel grothomex limom rdglim2a mp2an frsd-lem1 ax-mp frsd-lem13
      wlim cres a1i fveq1d fvres eqtrd iuneq2i 3eqtr4i ) FDGBEHDIJEIKLMLNOPZQUAZ
      RZAFAIZUTRZNZBUBRZAFVBBUCRZRZNFGSFUKVAVDTUDUEAQFGUSUFUGBGSVEVATCBDEUHUIAFV
      GVCVBFSZVGVBUTFULZRVCVHVBVFVIVFVITVHDEBCUJUMUNVBFUTUOUPUQUR $.
      $( [7-Sep-2014] $)

    frsd-lem16 $p |- ( A e. ( FRSD ` R ) -> |^| { x e. om | A e.
        ( ( FRSDlevel ` R ) ` x ) } e. om ) $=
      ( cfrsd cfv wcel cv cfrsdlevel com crab cint con0 wss c0 wne ssrab2 omsson
      sstri a1i wrex ciun frsd-lem17 eleq2i eliun biimpi sylbi rabn0 onint sseli
      sylibr syl2anc syl ) BCEFZGZBAHCIFFZGZAJKZLZURGZUSJGUOURMNZUROPZUTVAUOURJM
      UQAJQZRSTUOUQAJUAZVBUOBAJUPUBZGZVDUNVEBACDUCUDVFVDABJUPUEUFUGUQAJUHUKURUIU
      LURJUSVCUJUM $.
      $( [7-Sep-2014] $)

    frsd-lem14 $p |- ( A e. ( FRSD ` R ) -> ( ( FRSDrank ` R ) ` A ) =
        |^| { x e. om | A e.  ( ( FRSDlevel ` R ) ` x ) } ) $=
      ( cfrsd cfv wcel cfrsdrank cfrsdlevel com crab cint cmpt frsd-lem15 fveq1i
      va cv wceq frsd-lem16 eleq1 rabbidv inteqd eqid fvmptg mpdan syl5eq ) BCEF
      ZGZBCHFZFBPUGPQZAQCIFFZGZAJKZLZMZFZBUKGZAJKZLZBUIUOAPCDNOUHUSJGUPUSRABCDSP
      BUNUSUGJUOUJBRZUMURUTULUQAJUJBUKTUAUBUOUCUDUEUF $.
      $( [7-Sep-2014] $)

    frsd-lem18 $p |- ( ( FRSDlevel ` R ) ` (/) ) = (/) $=
      ( va vb c0 cfrsdlevel cfv cvv cn0 cv cfz cmap ciun cima cmpt crdg com cres
      c1 co frsd-lem13 fveq1i wcel wceq peano1 fvres ax-mp 0ex rdg0 3eqtri ) EAF
      GZGECHADICJSDJKTLTMNOZEPZQRZGZEUMGZEEUKUNCDABUAUBEQUCUOUPUDUEEQUMUFUGEULUH
      UIUJ $.
      $( [7-Sep-2014] $)

    frsd-lem19 $p |- ( A e. om -> ( ( FRSDlevel ` R ) ` suc A ) = ( R " U_ x e.
        NN0 ( ( ( FRSDlevel ` R ) ` A ) ^m ( 1 ... x ) ) ) ) $=
      ( va vb vc com wcel cvv cn0 cv c1 co cmap ciun cima c0 cfv wceq cfrsdlevel
      csuc cfz cmpt crdg cres con0 imaexg ax-mp frsd-lem9 rdgeq1 wa simpl oveq1d
      nnon iuneq2dv imaeq2d rdgsucmpt sylancl peano2 fvres syl adantr frsd-lem13
      3eqtr4d fveq1i oveq1i a1i iuneq2i imaeq2i 3eqtr4g ) BHIZBUBZEJCFKELMFLUCNO
      NPQUDZRUEZHUFZSZCAKBVPSZMALZUCNZONZPZQZVMCUASZSCAKBWDSZVTONZPZQVLVMVOSZCAK
      BVOSZVTONZPZQZVQWCVLBUGIWLJIZWHWLTBUOCJIWMDCWKJUHUIGRBCAKGLZVTONZPZQZWLVOJ
      VNGJWQUDZTVOWRRUETCEFGAUJRVNWRUKUIWNWITZWPWKCWSAKWOWJWSVSKIZULWNWIVTOWSWTU
      MUNUPUQURUSVLVMHIVQWHTBUTVMHVOVAVBVLWBWKCVLAKWAWJVLWAWJTWTVLVRWIVTOBHVOVAU
      NVCUPUQVEVMWDVPEFCDVDZVFWGWBCAKWFWAWFWATWTWEVRVTOBWDVPXAVFVGVHVIVJVK $.
    $}

    $( Given a finite sequence of finite ordinals, there is a finite ordinal
       which is ge all of them $)
    frsd-lem3 $p |- ( ( A e. NN0 /\ B e. ( om ^m ( 1 ... A ) ) ) ->
        E. a e. om A. b e. ( 1 ... A ) ( B ` b ) C_ a ) $=
      ( vd vc cv cfv wss c1 cfz co wral com wrex c0 wceq wa sseq1d wcel vf ve vg
      cc0 caddc cop csn grothomex oveq2 adantr fveq1 adantl raleqbidv rexbidv wb
      cun weq peano1 ral0 fz10 raleqi mpbir sseq2 ralbidv rcla4ev mp2an cn0 cmap
      w3a coa simplr simpll3 nnacl syl2anc wo simplll simpr omex mapfzconsval wi
      sylc simpll ad2antrl fveq2 rcla4va eqsstrd con0 nnon oaword1 syl2anr sstrd
      3ad2ant3 ex simpl ad2antrr ad2antlr oaword2 jaoi mpcom ralrimiva rexlimdva
      cbvralv sylib cbvrexv syl6ib mapfzind ) DGZEGZHZCGZIZDJFGZKLZMZCNOXGBHZXJI
      ZDJAKLZMZCNOXGPHZXJIZDJUDKLZMZCNOZXGUAGZHZXJIZDJUBGZKLZMZCNOZXGYDYGJUELZUC
      GZUFUGUPZHZXJIZDJYKKLZMZCNOZABNUCFEUBUAUHXLAQZXHBQZRZXNXRCNUUAXKXPDXMXQYSX
      MXQQYTXLAJKUIUJUUAXIXOXJYTXIXOQYSXGXHBUKULSUMUNXLUDQZXHPQZRZXNYBCNUUDXKXTD
      XMYAUUBXMYAQUUCXLUDJKUIUJUUCXKXTUOUUBUUCXIXSXJXGXHPUKSULUMUNFUBUQZEUAUQZRZ
      XNYICNUUGXKYFDXMYHUUEXMYHQUUFXLYGJKUIUJUUFXKYFUOUUEUUFXIYEXJXGXHYDUKSULUMU
      NXLYKQZXHYMQZRZXNYQCNUUJXKYODXMYPUUHXMYPQUUIXLYKJKUIUJUUIXKYOUOUUHUUIXIYNX
      JXGXHYMUKSULUMUNPNTXSPIZDYAMZYCURUULUUKDPMUUKDUSUUKDYAPUTVAVBYBUULCPNXJPQX
      TUUKDYAXJPXSVCVDVEVFYGVGTZYDNYHVHLTZYLNTZVIZYJYNXLIZDYPMZFNOZYRUUPYIUUSCNU
      UPXJNTZRZYIUUSUVAYIRZXJYLVJLZNTZYNUVCIZDYPMZUUSUVBUUTUUOUVDUUPUUTYIVKUUMUU
      NUUOUUTYIVLXJYLVMVNUVBXHYMHZUVCIZEYPMUVFUVBUVHEYPXHYHTZUVGXHYDHZQZRZXHYKQZ
      UVGYLQZRZVOZUVBXHYPTZRZUVHUVRUUPUVQUVPUUPUUTYIUVQVPUVBUVQVQYGYDNYLXHVRVSWA
      UVLUVRUVHVTZUVOUVLUVRUVHUVLUVRRZUVGXJUVCUVTUVGUVJXJUVIUVKUVRVKUVTUVIYIUVJX
      JIZUVIUVKUVRWBUVBYIUVLUVQUVAYIVQWCYFUWADXHYHDEUQYEUVJXJXGXHYDWDSWEVNWFUVBX
      JUVCIZUVLUVQUVAUWBYIUUTXJWGTZYLWGTZUWBUUPXJWHZUUOUUMUWDUUNYLWHWLZXJYLWIWJU
      JWCWKWMUVNUVSUVMUVNUVRUVHUVNUVRRUVGYLUVCUVNUVRWNUVBYLUVCIZUVNUVQUVBUWDUWCU
      WGUUPUWDUUTYIUWFWOUUTUWCUUPYIUWEWPYLXJWQVNWCWFWMULWRWSWTUVHUVEEDYPEDUQUVGY
      NUVCXHXGYMWDSXBXCUURUVFFUVCNXLUVCQUUQUVEDYPXLUVCYNVCVDVEVNWMXAUURYQFCNFCUQ
      UUQYODYPXLXJYNVCVDXDXEXF $.
      $( [6-Sep-2014] $)

    $( Substititution lemma for the FRSD step function $)
    frsd-lem5 $p |- ( A e. _V -> ( ( a e. _V |-> ( r " U_ b e. NN0 ( a ^m
        ( 1 ... b ) ) ) ) ` A ) = ( r " U_ b e. NN0 ( A ^m ( 1 ... b ) ) ) ) $=
      ( cv cn0 c1 cfz co cmap ciun cima cvv cmpt wceq wcel oveq1 adantr iuneq2dv
      imaeq2d eqid crn vex rnex imassrn ssexi fvmpt ) CABEZDFCEZGDEZHIZJIZKZLZUH
      DFAUKJIZKZLZMCMUNNZUIAOZUMUPUHUSDFULUOUSULUOOUJFPUIAUKJQRSTURUAUQUHUBUHBUC
      UDUHUPUEUFUG $.
      $( [6-Sep-2014] $)

    $( The iterative construction of FRSD preserves subsets $)
    frsd-lem4 $p |- ( ( B e. _V /\ A C_ B ) -> ( ( a e. _V |-> ( r "
        U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) ` A ) C_ ( ( a e. _V |-> ( r "
        U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) ` B ) ) $=
      ( cvv wcel wss cv cn0 c1 cfz co cmap ciun cima cfv ancoms wceq frsd-lem5
      wa cmpt wral ovex mapssi ralrimivw ss2iun imass2 3syl ssexg adantr 3sstr4d
      syl ) BFGZABHZUAZCIZEJAKEIZLMZNMZOZPZUQEJBUSNMZOZPZADFUQEJDIUSNMOPUBZQZBVF
      QZUPUTVCHZEJUCVAVDHVBVEHUPVIEJUOUNVIABUSKURLUDUERUFEJUTVCUGVAVDUQUHUIUPAFG
      ZVGVBSUOUNVJABFUJRACDETUMUNVHVESUOBCDETUKUL $.

    $( The FRSD construction produces a cumulative hierarchy 1 $)
    frsd-lem6 $p |- ( A e. om -> ( rec ( ( a e. _V |-> ( r " U_ b e. NN0 ( a ^m
        ( 1 ... b ) ) ) ) , (/) ) ` A ) C_ ( rec ( ( a e. _V |-> ( r "
        U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) , (/) ) ` suc A ) ) $=
      ( vd vc ve cv cvv co c0 cfv csuc wss wceq fveq2 suceq fveq2d sseq12d wcel
      cn0 c1 cfz cmap ciun cima cmpt crdg weq 0ex rdg0 0ss eqsstri com frsd-lem4
      wa fvex a1i biid frsd-lem9 fveq1i sseq12i 3imtr4i sylancom con0 rdgsuc syl
      nnon adantr suceloni 3syl 3sstr4d ex finds ) EHZCIBHZDUACHUBDHUCJUDJUEUFUG
      ZKUHZLZVOMZVRLZNKVRLZKMZVRLZNFHZVRLZWEMZVRLZNZWHWGMZVRLZNZAVRLZAMZVRLZNEFA
      VOKOZVSWBWAWDVOKVRPWPVTWCVRVOKQRSEFUIZVSWFWAWHVOWEVRPWQVTWGVRVOWEQRSVOWGOZ
      VSWHWAWKVOWGVRPWRVTWJVRVOWGQRSVOAOZVSWMWAWOVOAVRPWSVTWNVRVOAQRSWBKWDKVQUJU
      KWDULUMWEUNTZWIWLWTWIUPZWFVQLZWHVQLZWHWKWTWIWHITZXBXCNZXDXAWGVRUQURXDWIUPZ
      WFEIVPGUAVOUBGHUCJUDJUEUFUGZLZWHXGLZNXFXEWFWHBEGUOXFUSXBXHXCXIWFVQXGVPCDEG
      UTZVAWHVQXGXJVAVBVCVDWTWHXBOZWIWTWEVETZXKWEVHZKWEVQVFVGVIWTWKXCOZWIWTXLWGV
      ETXNXMWEVJKWGVQVFVKVIVLVMVN $.
      $( [6-Sep-2014] $)

    $( The FRSD construction produces a cumulative hierarchy 2 $)
    frsd-lem7 $p |- ( ( A e. om /\ B e. om /\ A C_ B ) -> ( rec ( ( a e. _V |-> ( r "
        U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) , (/) ) ` A ) C_
        ( rec ( ( a e. _V |-> ( r " U_ b e. NN0 ( a ^m ( 1 ... b ) ) ) ) ,
        (/) ) ` B ) ) $=
      ( vc vd com wcel wss w3a cvv cv cn0 co cfv wceq fveq2 sseq2d wa c1 cmap c0
      cfz ciun cima cmpt crdg simp2 simp1 simp3 csuc weq a1i frsd-lem6 ad3antrrr
      ssid simpr sstrd ex findsg syl21anc ) AHIZBHIZABJZKVDVCVEADLCMENDMUAEMUDOU
      BOUEUFUGUCUHZPZBVFPZJZVCVDVEUIVCVDVEUJVCVDVEUKVGFMZVFPZJVGVGJZVGGMZVFPZJZV
      GVMULZVFPZJZVIFGBAVJAQVKVGVGVJAVFRSFGUMVKVNVGVJVMVFRSVJVPQVKVQVGVJVPVFRSVJ
      BQVKVHVGVJBVFRSVLVCVGUQUNVMHIZVCTAVMJZTZVOVRWAVOTVGVNVQWAVOURVSVNVQJVCVTVO
      VMCDEUOUPUSUTVAVB $.
      $( [6-Sep-2014] $)

    frsd-lem12 $p |- ( FRSDrank ` r ) : ( FRSD ` r ) --> om $=
      ( va vb cv cfrsdlevel cfv wcel com crab cint cfrsd cfrsdrank wf frsd-lem16
      wral vex rgen frsd-lem15 fmpt mpbi ) BDZCDADZEFFGCHIJZHGZBUBKFZOUEHUBLFZMU
      DBUECUAUBAPZNQBUEHUCUFCBUBUGRST $.
      $( [7-Sep-2014] $)

    frsd-lem11 $p |- ( ( A e. om /\ B e. om /\ A C_ B ) -> ( ( FRSDlevel `
        r ) ` A ) C_ ( ( FRSDlevel ` r ) ` B ) ) $=
      ( va vb com wcel wss w3a cvv cv cn0 c1 co cfv wceq a1i fveq1d fvres eqtrd
      cfz cmap ciun cima cmpt crdg cfrsdlevel frsd-lem7 cres frsd-lem13 3ad2ant1
      c0 vex 3ad2ant2 3sstr4d ) AFGZBFGZABHZIADJCKZELDKMEKUANUBNUCUDUEULUFZOZBUT
      OZAUSUGOZOZBVCOZABCDEUHUPUQVDVAPURUPVDAUTFUIZOVAUPAVCVFVCVFPZUPDEUSCUMUJZQ
      RAFUTSTUKUQUPVEVBPURUQVEBVFOVBUQBVCVFVGUQVHQRBFUTSTUNUO $.
      $( [7-Sep-2014] $)

    frsd-lem10 $p |- ( A e. ( FRSD ` r ) -> A e. ( ( FRSDlevel ` r ) `
        ( ( FRSDrank ` r ) ` A ) ) ) $=
      ( va vb cv cfrsd cfv wcel cfrsdlevel com crab cint cfrsdrank wa wss c0 wne
      con0 fveq2 eleq2d ssrab2 omsson sstri cvv vex frsd-lem16 elex intex sylibr
      syl onint sylancr wceq elrab biimpi cbvrabv eleq2s simpr frsd-lem14 fveq2d
      weq 3syl eleqtrrd ) ABEZFGHZAACEZVDIGZGZHZCJKZLZVGGZAVDMGGZVGGVEVKVJHZVKJH
      ZAVLHZNZVPVEVJROVJPQZVNVJJRVICJUAUBUCVEVKUDHZVRVEVOVSCAVDBUEZUFVKJUGUJVJUH
      UIVJUKULVQVKADEZVGGZHZDJKZVJVKWDHVQWCVPDVKJWAVKUMWBVLAWAVKVGSTUNUOVIWCCDJC
      DVAVHWBAVFWAVGSTUPUQVOVPURVBVEVMVKVGCAVDVTUSUTVC $.
      $( [7-Sep-2014] $)


    $( Given a finite sequence of elements in the complete FRSD construction,
       there is a finite level of the constructon which contains the entire
       sequence $)
    ${
    $d x y r $. $d z w r $. $d u r $. $d u A $. $d u B $.
    frsd-lem2 $p |- ( ( A e. NN0 /\ B e. ( ( FRSD ` r ) ^m ( 1 ... A ) ) ) ->
        E. u e. om B e. ( ( ( FRSDlevel ` r ) ` u ) ^m ( 1 ... A ) ) ) $= 
      ( vb va vc wcel cv cfrsd cfv c1 cfz co cmap wa wss com simpr syl2anc simpl
      cn0 cfrsdrank ccom wral wrex cfrsdlevel frsd-lem12 a1i fvex ovex grothomex
      mapco1 frsd-lem3 simplr simpllr mapfv sylan ffvelrni syl weq fveq2 rcla4va
      wf sseq1d wb wfun cdm wceq ffun ax-mp mapfun adantl ad2antrr eleqtrrd fvco
      elmapdm syl3anc eqcomd adantlr mpbird frsd-lem11 frsd-lem10 sseldd mapdmres
      ralrimiva oveq1d eleq2d rcla4ev ex rexlimdva mpd ) BUBHZCDIZJKZLBMNZONHZPZ
      EIZWNUCKZCUDZKZFIZQZEWPUEZFRUFZCAIZWNUGKZKZWPONZHZARUFZWRWMXARWPONHZXFWMWQ
      UAWRWQWORWTVDZXMWMWQSXNWRDUHZUIWPCWOWTRWNJUJZLBMUKZULUMTBXAFEUNTWRXEXLFRWR
      XCRHZPZXEXLXSXEPZXRCXCXHKZWPONZHZXLWRXRXEUOXTWQGIZCKZYAHZGWPUEYCWMWQXRXEUP
      ZXTYFGWPXTYDWPHZPZYEWTKZXHKZYAYEYIYJRHZXRYJXCQZYKYAQYIYEWOHZYLXTWQYHYNYGWO
      CWPYDXQXPUQURZWORYEWTXOUSUTWRXRXEYHUPYIYMYDXAKZXCQZYIYHXEYQXTYHSXSXEYHUOXD
      YQEYDWPEGVAXBYPXCWSYDXAVBVEVCTXSYHYMYQVFXEXSYHPZYJYPXCYRYPYJYRWTVGZCVGZYDC
      VHZHYPYJVIYSYRXNYSXOWORWTVJVKUIWRYTXRYHWQYTWMWOCWPXQXPVLVMVNYRYDWPUUAXSYHS
      WRUUAWPVIZXRYHWQUUBWMWOCWPXQXPVQVMVNVOYDWTCVPVRVSVEVTWAYJXCDWBVRYIYNYEYKHY
      OYEDWCUTWDWFGWOCWPYAXQXPXCXHUJWETXKYCAXCRAFVAZXJYBCUUCXIYAWPOXGXCXHVBWGWHW
      ITWJWKWL $.
      $( [7-Sep-2014] $)
    $}

    $( Constructor rule for FRSD.  We prove that there is some level of the construction that contains all of the arguments, then show that that level + 1 contains the result. $)
    ${
    frsd-con.1 $e |- R e. _V $.
    frsd-con $p |- ( ( ( A e. NN0 /\ D e. _V ) /\ B e. ( ( FRSD ` R ) ^m
        ( 1 ... A ) ) /\ B R D ) -> D e. ( FRSD ` R ) ) $=
      ( va ve vc vb vd cn0 wcel wa cfv co cmap cv com wrex eleq2d cvv c1 cfz wbr
      cfrsd w3a cfrsdlevel wi wceq fveq2 oveq1d anbi2d rexbidv imbi12d frsd-lem2
      fveq1d vtocl adantlr 3adant3 csuc ciun cima simp1l ad2antrr oveq2d rcla4ev
      oveq2 sylancom eliun sylibr simpll3 breq1 syl2anc simp1r elimag syl mpbird
      wb frsd-lem19 ad2antlr ex peano2 adantl ssiun2s frsd-lem17 syl6sseqr sseld
      wss syld rexlimdva mpd ) AKLZCUALZMZBDUENZUBAUCOZPOZLZBCDUDZUFZBFQZDUGNZNZ
      WPPOZLZFRSZCWOLZWNWRXFWSWLWRXFWMWLBGQZUENZWPPOZLZMZBXAXHUGNZNZWPPOZLZFRSZU
      HWLWRMZXFUHGDEXHDUIZXLXRXQXFXSXKWRWLXSXJWQBXSXIWOWPPXHDUEUJUKTULXSXPXEFRXS
      XOXDBXSXNXCWPPXSXAXMXBXHDUGUJUPUKTUMUNFABGUOUQURUSWTXEXGFRWTXARLZMZXECXAUT
      ZXBNZLZXGYAXEYDYAXEMZYDCDHKXCUBHQZUCOZPOZVAZVBZLZYEYKIQZCDUDZIYISZYEBYILZW
      SYNYEBYHLZHKSZYOYAXEWLYQWTWLXTXEWLWMWRWSVCVDYPXEHAKYFAUIZYHXDBYRYGWPXCPYFA
      UBUCVGVETVFVHHBKYHVIVJWNWRWSXTXEVKYMWSIBYIYLBCDVLVFVMYEWMYKYNVRWTWMXTXEWLW
      MWRWSVNVDICDYIUAVOVPVQXTYDYKVRWTXEXTYCYJCHXADEVSTVTVQWAYAYCWOCYAYCJRJQZXBN
      ZVAZWOYAYBRLZYCUUAWHXTUUBWTXAWBWCJRYTYBYCYSYBXBUJWDVPJDEWEWFWGWIWJWK $.
      $( [7-Sep-2014] $)
    $}

    frsd-cong $p |- ( R e. _V -> ( ( ( A e. NN0 /\ D e. _V ) /\ B e. ( ( FRSD `
        R ) ^m ( 1 ... A ) ) /\ B R D ) -> D e. ( FRSD ` R ) ) ) $=
      ( cvv wcel cn0 wa cfrsd cfv c1 cfz co cmap wbr w3a wi c0 eleq2d eleq1 wceq
      cif fveq2 oveq1d breq 3anbi23d imbi12d 0ex elimhyp frsd-con dedth ) DEFZAG
      FCEFHZBDIJZKALMZNMZFZBCDOZPZCUNFZQUMBULDRUBZIJZUONMZFZBCVAOZPZCVBFZQDRDVAU
      AZUSVFUTVGVHUQVDURVEUMVHUPVCBVHUNVBUONDVAIUCZUDSBCDVAUEUFVHUNVBCVISUGABCVA
      ULVAEFREFDRDVAETRVAETUHUIUJUK $.
      $( [7-Sep-2014] $)

    ${
    $d x y z R $. $d x y z C $.
    frsd-indc.1 $e |- R e. _V $.
    frsd-indc.2 $e |- C e. _V $.
    frsd-indc.3 $e |- ( ( x e. NN0 /\ y e. ( C ^m ( 1 ... x ) ) /\ y R z ) -> z e. C ) $.
    frsd-indc $p |- ( FRSD ` R ) C_ C $=
      ( va vb cfv com cv wss c0 fveq2 sseq1d wcel wa cn0 vc cfrsdlevel ciun csuc
      cfrsd frsd-lem17 iunss wceq weq frsd-lem18 0ss eqsstri c1 cfz co cmap cima
      imaiun wral wbr wrex vex elima simpllr anass1rs ovex mapssi sylancl simplr
      sseldd simpr syl3anc ex rexlimdva syl5bi ssrdv ralrimiva sylibr frsd-lem19
      cvv syl5eqss wb adantr mpbird finds mprgbir ) EUEKILIMZEUBKZKZUCZDIEFUFWJD
      NWIDNZILILWIDUGJMZWHKZDNOWHKZDNUAMZWHKZDNZWOUDZWHKZDNZWKJUAWGWLOUHWMWNDWLO
      WHPQJUAUIWMWPDWLWOWHPQWLWRUHWMWSDWLWRWHPQJIUIWMWIDWLWGWHPQWNODEFUJDUKULWOL
      RZWQWTXAWQSZWTEATWPUMAMZUNUOZUPUOZUCUQZDNZXBXFATEXEUQZUCZDAETXEURXBXHDNZAT
      USXIDNXBXJATXBXCTRZSZCXHDCMZXHRBMZXMEUTZBXEVAXLXMDRZBXMEXECVBVCXLXOXPBXEXL
      XNXERZSZXOXPXRXOSZXKXNDXDUPUOZRXOXPXBXKXQXOVDXSXEXTXNXSWQDVTRXEXTNXLXOXQWQ
      XAWQXKXOXQSVDVEGWPDXDUMXCUNVFVGVHXLXQXOVIVJXRXOVKHVLVMVNVOVPVQATXHDUGVRWAX
      AWTXGWBWQXAWSXFDAWOEFVSQWCWDVMWEWFUL $.
      $( [7-Sep-2014] $)
    $}

    frsd-lem20 $p |- ( FRSD ` (/) ) = (/) $=
      ( va vb vc c0 cfrsd cfv wss wceq 0ex cv wbr cn0 wcel c1 cfz cmap cop df-br
      co noel pm2.21i sylbi 3ad2ant3 frsd-indc ss0 ax-mp ) DEFZDGUGDHABCDDIIBJZC
      JZDKZAJZLMUIDMZUHDNUKOSPSMUJUHUIQZDMZULUHUIDRUNULUMTUAUBUCUDUGUEUF $.
      $( [7-Sep-2014] $)

    ${
    $d x y z R $.  $d x y z C $.
    frsd-indcd.1 $e |- R e. _V $.
    frsd-indcd.2 $e |- C e. _V $.
    $( ~ dedth seems to run out of steam when the hypotheses have embedded quantifiers and discrete variable constraints $)
    frsd-indcd $p |- ( A. x e. NN0 A. y e. ( C ^m ( 1 ... x ) ) A. z e. _V
        ( y R z -> z e. C ) -> ( FRSD ` R ) C_ C ) $=
      ( va vd ve cv wcel wi wral co cn0 cfv com wss sseq1d vb vc vf wbr cvv cmap
      c1 cfz cfrsd cfrsdlevel ciun frsd-lem17 c0 csuc wceq imbi2d weq frsd-lem18
      fveq2 0ss eqsstri a1i w3a cima imaiun wa vex elima simpllr simp3 ad3antrrr
      wrex oveq2 oveq2d raleqdv rcla4va syl2anc simpl3 simpl2 ovex mapssi sseldd
      mpd simpr breq1 imbi1d breq2 eleq1 imbi12d rcla42va mpdan rexlimdva syl5bi
      syl21anc ex ssrdv ralrimiva iunss sylibr syl5eqss frsd-lem19 3ad2ant1 3exp
      wb mpbird finds impcom ) BKZCKZEUDZXIDLZMZCUENZBDUGAKZUHOZUFOZNZAPNZEUIQHR
      HKZEUJQZQZUKZDHEFULXRYADSZHRNYBDSXRYCHRXSRLXRYCXRUAKZXTQZDSZMXRUMXTQZDSZMX
      RUBKZXTQZDSZMZXRYIUNZXTQZDSZMXRYCMUAUBXSYDUMUOZYFYHXRYPYEYGDYDUMXTUSTUPUAU
      BUQZYFYKXRYQYEYJDYDYIXTUSTUPYDYMUOZYFYOXRYRYEYNDYDYMXTUSTUPUAHUQZYFYCXRYSY
      EYADYDXSXTUSTUPYHXRYGUMDEFURDUTVAVBYIRLZYLXRYOYTYLXRVCZYOEIPYJUGIKZUHOZUFO
      ZUKVDZDSZUUAUUEIPEUUDVDZUKZDIEPUUDVEUUAUUGDSZIPNUUHDSUUAUUIIPUUAUUBPLZVFZU
      CUUGDUCKZUUGLJKZUULEUDZJUUDVLUUKUULDLZJUULEUUDUCVGZVHUUKUUNUUOJUUDUUKUUMUU
      DLZVFZUUNUUOUURUUNVFZXMBDUUCUFOZNZUUOUUSUUJXRUVAUUAUUJUUQUUNVIUUAXRUUJUUQU
      UNYTYLXRVJVKXQUVAAUUBPAIUQZXMBXPUUTUVBXOUUCDUFXNUUBUGUHVMVNVOVPVQUUSUVAVFZ
      UUNUUOMZUUOUVCUUMUUTLUULUELZUVAUVDUVCUUDUUTUUMUVCYKDUELZUUDUUTSUVCXRYKUUKX
      RUUQUUNUVAYTYLXRUUJVRVKUUKYLUUQUUNUVAYTYLXRUUJVSVKWCUVFUVCGVBYJDUUCUGUUBUH
      VTWAVQUUKUUQUUNUVAVIWBUVEUVCUUPVBUUSUVAWDXLUVDUUMXIEUDZXKMBCUUMUULUUTUEBJU
      QXJUVGXKXHUUMXIEWEWFCUCUQUVGUUNXKUUOXIUULUUMEWGXIUULDWHWIWJWNUVCUVDVFUUNUU
      OUURUUNUVAUVDVIUVCUVDWDWCWKWKWOWLWMWPWQIPUUGDWRWSWTYTYLYOUUFXDXRYTYNUUEDIY
      IEFXATXBXEXCXFXGWQHRYADWRWSWT $.
      $( [7-Sep-2014] $)
    $}

    ${
    $d x y z R $.
    $d x y z C $.
    frsd-indcdd $p |- ( ( R e. _V /\ C e. _V ) -> ( A. x e. NN0 A. y e. ( C ^m ( 1 ... x ) ) A. z e. _V ( y R z -> z e. C ) -> ( FRSD ` R ) C_ C ) ) $=
      ( cvv wcel wa cv wi wral co cmap cn0 cfrsd wss c0 wceq ralbidv eleq1 oveq1
      wbr c1 cfz cfv cif eleq2 imbi2d raleqbidv sseq2 imbi12d breq imbi1d sseq1d
      fveq2 anbi2d anbi1d 0ex pm3.2i elimhyp2v simpli simpri frsd-indcd dedth2v
      ) EFGZDFGZHZBIZCIZEUBZVIDGZJZCFKZBDUCAIUDLZMLZKZANKZEOUEZDPZJVJVIVGDQUFZGZ
      JZCFKZBVTVNMLZKZANKZVRVTPZJVHVIVGEQUFZUBZWAJZCFKZBWDKZANKZWHOUEZVTPZJDEQQD
      VTRZVQWFVSWGWPVPWEANWPVMWCBVOWDDVTVNMUAWPVLWBCFWPVKWAVJDVTVIUGUHSUISDVTVRU
      JUKEWHRZWFWMWGWOWQWEWLANWQWCWKBWDWQWBWJCFWQVJWIWAVHVIEWHULUMSSSWQVRWNVTEWH
      OUOUNUKABCVTWHWHFGZVTFGZVGVEWSHWRWSHQFGZWTHWTWSHDEQQWPVFWSVEDVTFTUPWQVEWRW
      SEWHFTUQQVTRWTWSWTQVTFTUPQWHRWTWRWSQWHFTUQWTWTURURUSUTZVAWRWSXAVBVCVD $.
      $( [7-Sep-2014] $)
    $}

    frsd-ss $p |- ( ( A C_ B /\ B e. _V ) -> ( FRSD ` A ) C_ ( FRSD ` B ) ) $=
      ( vb vc va wss cvv wcel wa cfrsd cfv cv wbr wi wral c1 co cn0 w3a sylc cfz
      cmap ssexg fvex jctir simpllr 3simpb ad2antlr simplr2 simpll imp frsd-cong
      ssbrd 3jca ex ralrimivvva frsd-indcdd ) ABFZBGHZIZAGHZBJKZGHZICLZDLZAMZVEV
      BHZNZDGOCVBPELZUAQUBQZOEROAJKVBFUTVAVCABGUCBJUDUEUTVHECDRVJGUTVIRHZVDVJHZV
      EGHZSZIZVFVGVOVFIZUSVKVMIZVLVDVEBMZSVGURUSVNVFUFVPVQVLVRVNVQUTVFVKVLVMUGUH
      VKVLVMUTVFUIVOVFVRVOABVDVEURUSVNUJUMUKUNVIVDVEBULTUOUPECDVBAUQT $.
      $( [7-Sep-2014] $)

    frsd-ssrn $p |- ( R e. _V -> ( FRSD ` R ) C_ ran R ) $=
      ( vb vc va cvv wcel crn wa cv wbr wi wral c1 cfz co cmap cn0 cfrsd cfv vex
      wss rnexg ancli w3a brelrn a1i ralrimivvva frsd-indcdd sylc ) AEFZUJAGZEFZ
      HBIZCIZAJUNUKFKZCELBUKMDIZNOPOZLDQLARSUKUAUJULAEUBUCUJUODBCQUQEUOUJUPQFUMU
      QFUNEFUDHUMUNABTCTUEUFUGDBCUKAUHUI $.
      $( [7-Sep-2014] $)

    $( TODO: if K is an infinite cardinal such that all images of singletons under R have cardinality at most K, then ( FRSD ` R ) has cardinality at most K.  In other words finitary structures are countable $)
    $( TODO: provide an easy way to prove your constructed set is a function, using a local determinism predicate like that suggested below.  informally, if the recursive calls are determined by the local arguments, and the result is determined by the arguments and recursive results, the function will be defined in at most one way $)
    $( TODO: with a founded relation on the domain this can be strengthened to directly proving a dom $)
    $(
    $d u v w x y z A $.  $d u v w x y z B $.  $d u v w x y z R $.
    frsd-fun $p |- ( ( ( R e. _V /\ A e. _V /\ B e. _V ) /\ ( ran R C_ ( A X. B ) /\
        A. w e. U_ u e. NN0 ( ( A X. B ) ^m ( 1 ... u ) ) A. x e. ( A X. B )
            A. y e. U_ v e. NN0 ( ( A X. B ) ^m ( 1 ... v ) ) A. z e. ( A X. B )
                ( ( w R x /\ y R z /\ ( 1st ` x ) = ( 1st ` z ) ) ->
                    ( ( 1st o. w ) = ( 1st o. y ) /\ ( w = y -> x = z ) ) ) ) ) -> Fun ( FRSD ` R ) ) $= ? $.
    $)
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
    df-recparfa $a |- RecParFa = ( x e. NN0 |-> ( ( NN0 u. { ( Undef ` NN0 ) } ) ^m ( NN0 ^m ( 1 ... x ) ) ) ) $.

    $( All partial functions, regardless of arity $)
    df-recparf $a |- RecParF = U. ran RecParFa $.

    $( Arity of a partial function $)
    df-recarity $a |- RecArity = ( f e. RecParF |-> ( iota_ x e. NN0 f e. ( RecParFa ` x ) ) ) $.

    $( Total functions, a subset of partial functions $)
    df-rectotfa $a |- RecTotFa = ( x e. NN0 |-> ( NN0 ^m ( NN0 ^m ( 1 ... x ) ) ) ) $.
    df-rectotf $a |- RecTotF = U. ran RecTotFa $.
    $( we can use the same arity $)

    $( TODO: define RecPreList $)

    $( -- recursive function builders -- $)

    $( Zero recursive function $)
    df-reczer $a |- RecZer = ( x e. ( NN0 ^m ( 1 ... 0 ) ) |-> 0 ) $.
    $( Successor $)
    df-recsuc $a |- RecSuc = ( x e. ( NN0 ^m ( 1 ... 1 ) ) |-> ( ( x ` 1 ) + 1 ) ) $.
    $( Projector family: not defined for zero arity $)
    df-recprj $a |- RecPrj = ( x e. NN , y e. NN |-> ( z e. ( NN0 ^m ( 1 ... y ) ) |-> if ( x <_ y , ( z ` x ) , 0 ) ) ) $.
    $( Substitution $)
    df-recsub $a |- RecSub =
        ( x e. NN0 , y e. NN0 |->
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
    df-recprc $a |- RecPrc = ( x e. NN0 |->
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
    df-recsea $a |- RecSea = ( x e. NN0 |->
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
    $d a b c d e f g A $.
    $d a b c d e f g B $.
    $d a b c d e f g C $.
    $d a b c d e f g D $.
    $d a b c d e f g E $.

    dfrecparfa1 $p |- ( A e. NN0 -> ( RecParFa ` A ) = ( ( NN0 u. { ( Undef ` NN0 ) } ) ^m ( NN0 ^m ( 1 ... A ) ) ) ) $=
      ( va cn0 cund cfv csn cun c1 cv cfz cmap crecparfa wceq oveq2d df-recparfa
      co oveq2 ovex fvmpt ) BACCDEFGZCHBIZJPZKPZKPTCHAJPZKPZKPCLUAAMZUCUETKUFUBU
      DCKUAAHJQNNBOTUEKRS $.
      $( [4-Sep-2014] $)

    dfrectotfa1 $p |- ( A e. NN0 -> ( RecTotFa ` A ) = ( NN0 ^m ( NN0 ^m ( 1 ... A ) ) ) ) $=
      ( va cn0 c1 cv cfz cmap crectotfa wceq oveq2 oveq2d df-rectotfa ovex fvmpt
      co ) BACCDBEZFOZGOZGOCCDAFOZGOZGOCHPAIZRTCGUAQSCGPADFJKKBLCTGMN $.
      $( [4-Sep-2014] $)

    totfa-is-parfa $p |- ( A e. NN0 -> ( RecTotFa ` A ) C_ ( RecParFa ` A ) ) $=
      ( cn0 wcel crectotfa cfv cund csn cun c1 cfz co cmap crecparfa dfrectotfa1
      wss ssun1 a1i nn0ex snex unex ovex mapss syl eqsstrd dfrecparfa1 sseqtr4d
      ) ABCZADEZBBFEZGZHZBIAJKZLKZLKZAMEUGUHBUMLKZUNANUGBUKOZUOUNOUPUGBUJPQBUKUM
      BUJRUISTBULLUAUBUCUDAUEUF $.
      $( [4-Sep-2014] $)

    totfa-fn $p |- RecTotFa Fn NN0 $=
      ( va cn0 c1 cv cfz cmap cvv wcel crectotfa wfn df-rectotfa fnmpt ovex mprg
      co a1i ) BBCADZEOFOZFOZGHZIBJABABSIGAKLTQBHBRFMPN $.
      $( [4-Sep-2014] $)

    parfa-fn $p |- RecParFa Fn NN0 $=
      ( va cn0 cund cfv csn cun c1 cv cfz co cmap cvv wcel crecparfa df-recparfa
      wfn fnmpt ovex a1i mprg ) BBCDEFZBGAHZIJKJZKJZLMZNBPABABUDNLAOQUEUBBMUAUCK
      RST $.
      $( [4-Sep-2014] $)

    dfrectotf1 $p |- RecTotF = U_ a e. NN0 ( RecTotFa ` a ) $=
      ( crectotf crectotfa crn cuni cn0 cv cfv ciun df-rectotf wfn wceq totfa-fn
      fniunfv ax-mp eqtr4i ) BCDEZAFAGCHIZJCFKRQLMAFCNOP $.
      $( [4-Sep-2014] $)

    dfrecparf1 $p |- RecParF = U_ a e. NN0 ( RecParFa ` a ) $=
      ( crecparf crecparfa crn cuni cn0 cv cfv ciun df-recparf wfn wceq parfa-fn
      fniunfv ax-mp eqtr4i ) BCDEZAFAGCHIZJCFKRQLMAFCNOP $.
      $( [4-Sep-2014] $)

    totf-is-parf $p |- RecTotF C_ RecParF $=
      ( crectotf cn0 crectotfa cfv ciun crecparf dfrectotf1 crecparfa wss ss2iun
      va cv totfa-is-parfa mprg dfrecparf1 sseqtr4i eqsstri ) AKBKLZCDZEZFKGTKBR
      HDZEZFSUAITUBIKBKBSUAJRMNKOPQ $.

    totfa-is-parfa-g $p |- ( RecTotFa ` A ) C_ ( RecParFa ` A ) $=
      ( cn0 wcel crectotfa cfv crecparfa wss totfa-is-parfa wn cdm wceq totfa-fn
      c0 wfn fndm ax-mp eqcomi eleq2i notbii biimpi syl 0ss a1i eqsstrd pm2.61i
      ndmfv ) ABCZADEZAFEZGAHUGIZUHMUIUJADJZCZIZUHMKUJUMUGULBUKAUKBDBNUKBKLBDOPQ
      RSTADUFUAMUIGUJUIUBUCUDUE $.
      $( [5-Sep-2014] $)

    $( use fz1eqb, elfvdm $)
    parfa-domlem $p |- ( A e. ( RecParFa ` B ) -> B e. NN0 ) $=
      ( crecparfa cfv wcel cdm cn0 elfvdm id wceq wfn parfa-fn ax-mp a1i eleqtrd
      fndm syl ) ABCDEBCFZEZBGEABCHSBRGSIRGJZSCGKTLGCPMNOQ $.
      $( [4-Sep-2014] $)

    totfa-domlem $p |- ( A e. ( RecTotFa ` B ) -> B e. NN0 ) $=
      ( crectotfa cfv wcel cdm cn0 elfvdm id wceq wfn totfa-fn ax-mp a1i eleqtrd
      fndm syl ) ABCDEBCFZEZBGEABCHSBRGSIRGJZSCGKTLGCPMNOQ $.
      $( [4-Sep-2014] $)

    $( use elmapg to derive C : (^A) --> NN0 and C : (^B) ---> NN0 $)
    $( use fdm to get (^A) = dom C = (^B) $)
    parfa-disjoint $p |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( C e. ( RecParFa ` A ) /\ C e. ( RecParFa ` B ) ) ) -> A = B ) $=
      ( cn0 wcel wa crecparfa cfv cfz wceq cund csn cun cmap dfrecparfa1 eleqtrd
      c1 co nn0ex ovex simprl ad2antrr simprr ad2antlr jca snex unex mapcan0 cc0
      0nn0 mapcan1 3syl fz1eqb biimpd imp syldan ) ADEZBDEZFZCAGHZEZCBGHZEZFZQAI
      RZQBIRZJZABJZUSVDFZCDDKHZLZMZDVENRZNRZEZCVLDVFNRZNRZEZFVMVPJVGVIVOVRVICUTV
      NUSVAVCUAUQUTVNJURVDAOUBPVICVBVQUSVAVCUCURVBVQJUQVDBOUDPUECVLVMVLVPDVKSVJU
      FUGZDVENTVSDVFNTUHUIDVEVFUJQAITQBITSUKULUSVGVHUSVGVHABUMUNUOUP $.
      $( [4-Sep-2014] $)

    parfa-disjoint-g $p |- ( ( C e. ( RecParFa ` A ) /\ C e. ( RecParFa ` B ) ) -> A = B ) $=
      ( cn0 wcel crecparfa cfv wceq parfa-domlem anim12i parfa-disjoint mpancom
      wa ) ADEZBDEZMCAFGEZCBFGEZMABHPNQOCAICBIJABCKL $.
      $( [5-Sep-2014] $)

    dfarity1 $p |- ( A e. RecParF -> ( RecArity ` A ) = ( iota_ a e. NN0 A e. ( RecParFa ` a ) ) ) $=
      ( vb crecparfa cfv wcel cn0 crio crecparf crecarity wceq eleq1 df-recarity
      cv riotabidv riotaex fvmpt ) CACNZBNDEZFZBGHASFZBGHIJRAKTUABGRASLOBCMUABGP
      Q $.
      $( [4-Sep-2014] $)

    parfa-is-parf $p |- ( A e. NN0 -> ( RecParFa ` A ) C_ RecParF ) $=
      ( va cn0 wcel crecparfa cfv cv crecparf fveq2 ssiun2s dfrecparf1 syl6sseqr
      ciun ) ACDAEFZBCBGZEFZMHBCPANOAEIJBKL $.
      $( [4-Sep-2014] $)

    totfa-is-totf $p |- ( A e. NN0 -> ( RecTotFa ` A ) C_ RecTotF ) $=
      ( va cn0 wcel crectotfa cfv cv crectotf fveq2 ssiun2s dfrectotf1 syl6sseqr
      ciun ) ACDAEFZBCBGZEFZMHBCPANOAEIJBKL $.
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
      ( va crecparfa cfv wcel cn0 crecarity wceq parfa-domlem wa cv crecparf wss
      crio parfa-is-parf adantl simpl sseldd simpl1 syl parfa-disjoint-g syl2anc
      dfarity1 w3a simpr fveq2 eqcomd eleqtrd impbida riota5 eqtrd mpdan ) BADEZ
      FZAGFZBHEZAIBAJUOUPKZUQBCLZDEZFZCGOZAURBMFUQVBIURUNMBUPUNMNUOAPQUOUPRSBCUD
      UAUOVACGAUOUPUSGFZUEZVAUSAIZVDVAKVAUOVEVDVAUFUOUPVCVATUSABUBUCVDVEKBUNUTUO
      UPVCVETVEUNUTIVDVEUTUNUSADUGUHQUIUJUKULUM $.
      $( [5-Sep-2014] $)

    $( possible to factor out "partition of sets"/"rank function" concept $)
    arity-defined $p |- ( A e. RecParF -> ( RecArity ` A ) e. NN0 ) $=
      ( va crecparf wcel cv crecparfa cfv cn0 wrex dfparf2 dfarity4 parfa-domlem
      crecarity eqeltrd rexlimivw sylbi ) ACDABEZFGDZBHIAMGZHDZABJRTBHRSQHQAKAQL
      NOP $.

    arity-fn $p |- RecArity Fn RecParF $=
      ( va vb cv crecparfa cfv wcel cn0 crio cvv crecparf wral crecarity riotaex
      wfn rgenw df-recarity fnmpt ax-mp ) ACBCDEFZBGHZIFZAJKLJNUAAJSBGMOAJTLIBAP
      QR $.
      $( [4-Sep-2014] $)

    arity-fun $p |- RecArity : RecParF --> NN0 $=
      ( va crecparf cn0 crecarity wf wfn cv cfv wcel wral arity-fn arity-defined
      ffnfv rgen mpbir2an ) BCDEDBFAGZDHCIZABJABCDMKQABPLNO $.
      $( [4-Sep-2014] $)

    arity-df2 $p |- ( ( A e. NN0 /\ B e. RecParF ) -> ( B e. ( RecParFa ` A ) <-> ( RecArity ` B ) = A ) ) $=
      ( va vb cn0 wcel crecparf wa crecparfa cfv cv crio wceq crecarity dfarity1
      wreu wb adantl arity-defined eqeltrrd nn0ex sylibr ax-17 a17d fveq2 eleq2d
      riotaclb riota2f syldan eqeq1d bitr4d ) AEFZBGFZHZBAIJZFZBCKZIJZFZCELZAMZB
      NJZAMULUMUSCEPZUPVAQUNUTEFVCUNVBUTEUMVBUTMULBCORZUMVBEFULBSRTUSCEUAUGUBUSU
      PCDEADKAFCUCULUPCUDUQAMURUOBUQAIUEUFUHUIUNVBUTAVDUJUK $.
      $( [4-Sep-2014] $)

    arity-df3 $p |- ( B e. ( RecParFa ` A ) <-> ( B e. RecParF /\ ( RecArity ` B ) = A ) ) $=
      ( crecparfa cfv wcel crecparf crecarity wceq wa parfa-domlem parfa-is-parf
      cn0 wss adantl simpl sseldd mpdan dfarity4 jca simpr wb eqeltrrd arity-df2
      arity-defined adantr syl2anc mpbird impbii ) BACDZEZBFEZBGDZAHZIZUJUKUMUJA
      LEZUKBAJUJUOIUIFBUOUIFMUJAKNUJUOOPQABRSUNUJUMUKUMTZUNUOUKUJUMUAUNULALUPUKU
      LLEUMBUDUEUBUKUMOABUCUFUGUH $.
      $( [4-Sep-2014] $)

    arity-dftot $p |- ( B e. ( RecTotFa ` A ) <-> ( B e. RecTotF /\ ( RecArity ` B ) = A ) ) $=
      ( vd crectotfa cfv wcel crectotf crecarity wceq totfa-domlem totfa-is-totf
      wa cn0 wss simpl crecparfa crecparf totfa-is-parfa-g sseli simpr arity-df3
      adantl sseldd biimpi 3syl adantr jca mpdan totf-is-parf sseldi sylanbrc cv
      wrex wi dftotf2 parfa-disjoint-g sylan fveq2d eleqtrd rexlimivw sylbi sylc
      ex impbii ) BADEZFZBGFZBHEAIZLZVFAMFZVIBAJVFVJLZVGVHVKVEGBVJVEGNVFAKUBVFVJ
      OUCVFVHVJVFBAPEZFZBQFZVHLZVHVEVLBARSVMVOABUAZUDVNVHTUEUFUGUHVIVGVMVFVGVHOZ
      VIVNVHVMVIGQBUIVQUJVGVHTVPUKVGBCULZDEZFZCMUMVMVFUNZBCUOVTWACMVTVMVFVTVMLZB
      VSVEVTVMOWBVRADVTBVRPEZFVMVRAIVSWCBVRRSVRABUPUQURUSVCUTVAVBVD $.
      $( [4-Sep-2014] $)
$}

${
    $d a b c d e f g $.

    fun-is-totf $p |- ( ( A e. NN0 /\ B : ( NN0 ^m ( 1 ... A ) ) --> NN0 ) -> B e. ( RecTotFa ` A ) ) $=
      ( cn0 wcel c1 cfz co cmap wf crectotfa cfv nn0ex ovex elmap biimpri adantl
      wa wceq dfrectotfa1 adantr eleqtrrd ) ACDZCEAFGZHGZCBIZQBCUDHGZAJKZUEBUFDZ
      UBUHUECUDBLCUCHMNOPUBUGUFRUEASTUA $.
      $( [5-Sep-2014] $)

    compactified-nn-ex $p |- ( NN0 u. { ( Undef ` NN0 ) } ) e. _V $=
      ( cn0 cund cfv csn nn0ex snex unex ) AABCZDEHFG $.
      $( [5-Sep-2014] $)

    fun-is-parf $p |- ( ( A e. NN0 /\ B : ( NN0 ^m ( 1 ... A ) ) --> ( NN0 u. { ( Undef ` NN0 ) } ) ) -> B e. ( RecParFa ` A ) ) $=
      ( cn0 wcel c1 cfz co cmap cund cfv csn cun wf crecparfa compactified-nn-ex
      wa ovex elmap biimpri adantl wceq dfrecparfa1 adantr eleqtrrd ) ACDZCEAFGZ
      HGZCCIJKLZBMZPBUHUGHGZANJZUIBUJDZUEULUIUHUGBOCUFHQRSTUEUKUJUAUIAUBUCUD $.
      $( [5-Sep-2014] $)

    zer-fn    $p |- RecZer : ( NN0 ^m ( 1 ... 0 ) ) --> NN0 $=
      ( va cc0 cn0 wcel c1 co cmap creczer wf wral df-reczer fmpt biimpi cv 0nn0
      cfz a1i mprg ) BCDZCEBPFGFZCHIZATSATJUAATCBHAKLMSANTDOQR $.
      $( [5-Sep-2014] $)

    zer-totfa $p |- RecZer e. ( RecTotFa ` 0 ) $=
      ( cc0 cn0 wcel c1 cfz co cmap creczer wf crectotfa 0nn0 zer-fn fun-is-totf
      cfv mp2an ) ABCBDAEFGFBHIHAJNCKLAHMO $.
      $( [5-Sep-2014] $)

    $( needs more lemmas about elements of integer ranges $)
    suc-fn    $p |- RecSuc : ( NN0 ^m ( 1 ... 1 ) ) --> NN0 $=
      ( va c1 cv cfv caddc co cn0 wcel cfz cmap crecsuc wf wral df-recsuc biimpi
      fmpt nn0ex ovex elmap wceq csn eqid1 1nn0 elexi elsnc mpbir cz 1z eleqtrri
      fzsn ax-mp ffvelrn mpan2 peano2nn0 3syl mprg ) BACZDZBEFZGHZGBBIFZJFZGKLZA
      VBUTAVBMVCAVBGUSKANPOUQVBHZVAGUQLZURGHZUTVDVEGVAUQQBBIRSOVEBVAHVFBBUAZVABV
      GHBBTBUBBBBGUCUDUEUFBUGHVAVGTUHBUJUKUIVAGBUQULUMURUNUOUP $.
      $( [5-Sep-2014] $)

    suc-totfa $p |- RecSuc e. ( RecTotFa ` 1 ) $=
      ( c1 cn0 wcel cfz co cmap crecsuc wf crectotfa cfv 1nn0 suc-fn fun-is-totf
      mp2an ) ABCBAADEFEBGHGAIJCKLAGMN $.
      $( [5-Sep-2014] $)

    prj-value $p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) = ( a e. ( NN0 ^m ( 1 ... B ) ) |-> if ( A <_ B , ( a ` A ) , 0 ) ) ) $= ? $.
    prj-val2  $p |- ( ( A e. NN /\ B e. NN /\ A <_ B ) -> ( A RecPrj B ) = ( z e. ( NN0 ^m ( 1 ... B ) ) |-> ( z ` A ) ) ) $= ? $.
    prj-val3  $p |- ( ( ( A e. NN /\ B e. NN /\ A <_ B ) /\ C e. ( NN0 ^m ( 1 ... B ) ) ) -> ( ( A RecPrj B ) ` C ) = ( C ` A ) ) $= ? $.
    prj-fun   $p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) Fun ( NN0 ^m ( 1 ... B ) ) ) $= ? $.
    prj-fn    $p |- ( ( A e. NN /\ B e. NN ) -> ( A RecPrj B ) : ( NN0 ^m ( 1 ... B ) ) --> NN0 ) $= ? $.
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

    $( We may not need a full induction schema; coinduction + cantor pair comparison lemmata implies that ordinary induction on NN0 can be lifted to induction here $)
    $( generally have +, -, *, /, 1st_n, 2nd_n, ,n, all constants, bounded looping, bounded iota, composition (normal subsititute-y), anything else we might need $)
$}

${
    $( tree recursion lemma: reifies the stacks, takes p.r. f, g, fc, gc, h and builds F:
       F(x) = h( x, fc(x) ? F(f(x)) : 0, gc(x) ? F(g(x)) : 0 )  details TBD $)
    $( F is general recursive $)
    $( F is total if there exists T : NN --> On which is decreased by f and g $)
    $( F is primitive recursive if there exists T : NN -> NN which is primitve recursive and T(f(x)) + T(g(x)) < T(x) $)
$}

${
    $( succinct encodings $)
    $( ( x -> 2*x ) has some number < A = A ^ ( k ^ 0 ) $)
    $( ( x -> 2*x + 1 ) has some number < A ^ ( k ^ 0 ) $)
    $( if A >= A_base and f# < A and g# < A, (f o. g)# < A ^ k $)
    $( for i = 0, all N < 2 ^ ( 2 ^ i ), ( x -> (2^(2^i))*x + N )# < A ^ ( k ^ 0 ) $)
    $( for i >= 0, N < 2 ^ ( 2 ^ ( i + 1 ) ), ( x -> (2^(2^(i+1)))*x + N ) = ( x -> (2^(2^i))*x + A ) o. ( x -> (2^(2^i))*x + B ) for A,B determined by the division theorem $)
    $( for i >= 0, N < 2 ^ ( 2 ^ i ), ( x -> (2^(2^i))*x + N )# < A ^ ( k ^ i ) by induction $)
    $( for x >= 0, exists i such that x <_ ( 2 ^ ( 2 ^ i ) ) <_ ( x ^ 2 ) $)
    $( for x >= 0, ( () -> x )# < ( A ^ ( k ^ i ) ) -> log( () -> x ) <
       log( A ^ ( k ^ i ) ) = (k^i).log(A) = (2^i)^(log(k)/log(2))*log(A) <
       log(A)/log(2)*log(2^2^i)^(log(k)/log(2)) <
       log(A)/log(2) * log(x^2) ^ (log(k)/log(2)) = K * log(x) ^ L $)

$}

${
    $( Raphael Robinson's inductive intrinsic characterization of the one-argument p.r. functions.  use ( ( ( x ,n b ) - a ) ,n a ) as an increment-friendly pair that works with our lemmas $)
$}

${
    $( Peter-Ackermann function $)
    $( A(0)   = Suc $)
    $( A(i+1) = Prc(A(i),A(i)) $)
    $( A(i,_) is primitive recursive at level i $)
    $( let P(i) = for all p.r. F at level i and all [x...], F(x...) <_ A(max(x...)) $)
    $( P(0) : F at 0 is Zer, Suc, or Prj $)
    $( P(i+1) : zer/suc/prj handled.  either Sub or Prc remains $)
    $( Prj(f,g)(const,N) : note g(const) <_ A(const), for all v >= max(const) (f(const,i) <_ partial ackerman) $)
    $( requires A_i(i) is monotonic $)
    $( requires definition of iterates of A $)
    $( Sub(f,g...) : note all g values are less than A_i(in), so the result is less than A_i(A_i(in)) $)
    $( requires: A(i,A(i,x)) <_ A(i+1,x) $)
    $( requires: A(i,j) is strictly monotonic in i,j $)
    $( A(j,j) is not dominated by A(i,j) for any fixed i $)
    $( A(j,j) is not primitive recursive $)
    $( suppose phi(f#, x) were primitive recursive.  then f(x) <_ A(i,max(f#,x)) for some i and all pr f $)
    $( let f = A(i+1,_), y = f#.  A(i+1,y) = f(y) <_ A(i,max(f#,y)) = A(i,y), contradicting A(i+1,y) > A(i,j) $)
    $( thus phi is not pr.  it will be shown gr in the next section $)
    $( todo: this does not seem to quite be the standard Peter-Ackerman function, which has A(i+1) = Prc(A(i),1).  I like how much sharper my version is, the fastest-growing PR function of a given rank.  OTOH it's a little harder to calculate $)
$}

${
    $( Relativization and the Turing Degrees? $)
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

$( ---- MULTIVARIATE POLYNOMIALS ---- $)
$( Define multivariate polynomials and prove that they include constants and projections and are closed under addition, multiplication, and renaming of variables. Later we will also need the property that polynomial functions are computable. $)
$( in particular, we don't need normal forms, so just define these as a recursive set $)

$c MVZPolyF MVZPolyF_R $.
cmvzpolyf $a class MVZPolyF $.
cmvzpolyf_r $a class MVZPolyF_R $.

$( the smallest set of integer functions containing constants and projectors and closed under +, * $)

${
$d x y z u v w $.
df-mvzpolyf-r $a |- MVZPolyF_R = ( x e. NN0 |-> { <. y , z >. | ( (
    y e. U_ u e. NN0 ( ( ZZ ^m ( ZZ ^m ( 1 ... x ) ) ) ^m ( 1 ... u ) ) /\
    z e. ( ZZ ^m ( ZZ ^m ( 1 ... x ) ) )
) /\ (
    ( y = (/) /\ (
        E. u e. ( 1 ... x ) z = ( v e. ( ZZ ^m ( 1 ... x ) ) |-> ( v ` u ) ) \/
        E. u e. ZZ z = ( v e. ( ZZ ^m ( 1 ... x ) ) |-> u )
    ) ) \/
    E. u e. ( ZZ ^m ( ZZ ^m ( 1 ... x ) ) )
    E. v e. ( ZZ ^m ( ZZ ^m ( 1 ... x ) ) ) (
        y = { <. 1 , u >. , <. 2 , v >. } /\
        ( z = ( w e. ( ZZ ^m ( 1 ... x ) ) |-> ( ( u ` w ) + ( v ` w ) ) ) \/
          z = ( w e. ( ZZ ^m ( 1 ... x ) ) |-> ( ( u ` w ) x. ( v ` w ) ) ) )
    )
) ) } ) $.

df-mvzpolyf $a |- MVZPolyF = ( x e. NN0 |-> ( FRSD ` ( MVZPolyF_R ` x ) ) ) $.
$}

${
    $d a b c d e f g h i j A $.
    $d a b c d e f g h i j B $.
    $d a b c d e f g h i j C $.
    $d a b c d e f g h i j D $.
    $d a b c d e f g h i j M $.
    $d a b c d e f g h i j N $.
    $d a b c d e f g h i j N $.
    $d a b c d e f g h i j u $.
    $d a b c d e f g h i j v $.
    $d a b c d e f g h i j w $.
    $d a b c d e f g h i j x $.
    $d a b c d e f g h i j y $.
    $d a b c d e f g h i j z $.
    $d a b c d e f g h i j ph $.
    $d a b c d e f g h i j ps $.
    $d a b c d e f g h i j ch $.

    ${
    $d u v w x y z a N $.

    dfmvzpolyf-r1 $p |- ( N e. NN0 -> ( MVZPolyF_R ` N ) = { <. y , z >. | ( (
        y e. U_ u e. NN0 ( ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) ^m ( 1 ... u ) ) /\
        z e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) )
    ) /\ (
        ( y = (/) /\ (
            E. u e. ( 1 ... N ) z = ( v e. ( ZZ ^m ( 1 ... N ) ) |-> ( v ` u ) ) \/
            E. u e. ZZ z = ( v e. ( ZZ ^m ( 1 ... N ) ) |-> u )
        ) ) \/
        E. u e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) )
        E. v e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) (
            y = { <. 1 , u >. , <. 2 , v >. } /\
            ( z = ( w e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` w ) + ( v ` w ) ) ) \/
              z = ( w e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` w ) x. ( v ` w ) ) ) )
        )
    ) ) } ) $=
      ( cv cn0 cz c1 cfz co cmap wcel wa wceq cmpt wrex wo eqidd va ciun cfv cop
      c0 c2 cpr caddc cmul copab cmvzpolyf_r oveq2 oveq2d oveq1d adantr iuneq2dv
      eleq2d anbi12d mpteq12dv eqeq2d rexeqbidv rexbidv anbi2d mpteq12d opabbidv
      orbi12d ax-17 df-mvzpolyf-r cxp nn0ex ovex iunex xpex opabssxp ssexi fvmpt
      ) UAFAGZEHIIJUAGZKLZMLZMLZJEGZKLZMLZUBZNZBGZWANZOZVQUEPZWGDVTWBDGZUCZQZPZE
      VSRZWGDVTWBQZPZEIRZSZOZVQJWBUDUFWKUDUGPZWGCVTCGZWBUCZXBWKUCZUHLZQZPZWGCVTX
      CXDUILZQZPZSZOZDWARZEWARZSZOZABUJVQEHIIJFKLZMLZMLZWCMLZUBZNZWGXSNZOZWJWGDX
      RWLQZPZEXQRZWGDXRWBQZPZEIRZSZOZXAWGCXRXEQZPZWGCXRXHQZPZSZOZDXSRZEXSRZSZOZA
      BUJZHUKVRFPZXPUUBABUUDWIYDXOUUAUUDWFYBWHYCUUDWEYAVQUUDEHWDXTUUDWDXTPWBHNUU
      DWAXSWCMUUDVTXRIMUUDVSXQIMVRFJKULZUMZUMZUNUOUPUQUUDWAXSWGUUGUQURUUDWTYLXNY
      TUUDWSYKWJUUDWOYGWRYJUUDWNYFEVSXQUUEUUDWMYEWGUUDDVTWLXRWLUUFUUDWLTUSUTVAUU
      DWQYIEIUUDWPYHWGUUDDVTWBXRWBUUFUUDWBTUSUTVBVFVCUUDXMYSEWAXSUUGUUDXLYRDWAXS
      UUGUUDXKYQXAUUDXGYNXJYPUUDXFYMWGUUDCVTXEXRXEUUDCVGUUFUUDXETVDUTUUDXIYOWGUU
      DCVTXHXRXHUUFUUDXHTUSUTVFVCVAVAVFURVEUAABCDEVHUUCYAXSVIYAXSEHXTVJXSWCMVKVL
      IXRMVKVMUUAABYAXSVNVOVP $.
      $( [8-Sep-2014] $)

    $d A u $.  $d A v $.  $d B u $.  $d B v $.
    dfmvzpolyf-r2 $p |- ( ( N e. NN0 /\ A e. _V /\ B e. _V ) -> (
        A ( MVZPolyF_R ` N ) B <-> ( (
            A e. U_ u e. NN0 ( ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) ^m ( 1 ... u ) ) /\
            B e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) )
        ) /\ (
            ( A = (/) /\ (
                E. u e. ( 1 ... N ) B = ( v e. ( ZZ ^m ( 1 ... N ) ) |-> ( v ` u ) ) \/
                E. u e. ZZ B = ( v e. ( ZZ ^m ( 1 ... N ) ) |-> u )
            ) ) \/
            E. u e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) )
            E. v e. ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) (
                A = { <. 1 , u >. , <. 2 , v >. } /\
                ( B = ( w e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` w ) + ( v ` w ) ) ) \/
                  B = ( w e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` w ) x. ( v ` w ) ) ) )
            )
        ) )
    ) ) $=
      ( va vb wcel cvv cfv cv cz co wa c0 wceq wrex wo eqidd cn0 w3a cmvzpolyf_r
      wbr cop c1 cfz cmap ciun cmpt c2 cpr caddc cmul copab wb a1i dfmvzpolyf-r1
      df-br 3ad2ant1 eleq2d simpl eleq12d simpr anbi12d id1 eqeqan12d eqeqan12rd
      rexbidv orbi12d eqeq1d opelopabga 3adant1 3bitrd ) FUAIZDJIZEJIZUBZDEFUCKZ
      UDZDEUEZVSIZWAGLZCUAMMUFFUGNZUHNZUHNZUFCLZUGNUHNUIZIZHLZWFIZOZWCPQZWJBWEWG
      BLZKUJZQZCWDRZWJBWEWGUJZQZCMRZSZOZWCUFWGUEUKWNUEULZQZWJAWEALZWGKZXEWNKZUMN
      UJZQZWJAWEXFXGUNNUJZQZSZOZBWFRZCWFRZSZOZGHUOZIZDWHIZEWFIZOZDPQZEWOQZCWDRZE
      WRQZCMRZSZOZDXCQZEXHQZEXJQZSZOZBWFRZCWFRZSZOZVTWBUPVRDEVSUSUQVRVSXRWAVOVPV
      SXRQVQGHABCFURUTVAVPVQXSYRUPVOXQYRGHDEJJWCDQZWJEQZOZWLYBXPYQUUAWIXTWKYAUUA
      WCDWHWHYSYTVBUUAWHTVCUUAWJEWFWFYSYTVDZUUAWFTVCVEUUAXBYIXOYPUUAWMYCXAYHYSYT
      WCDPPYSVFZYTPTVGUUAWQYEWTYGUUAWPYDCWDYTYSWJEWOWOYTVFZYSWOTVHVIUUAWSYFCMYTY
      SWJEWRWRUUDYSWRTVHVIVJVEUUAXNYOCWFUUAXMYNBWFUUAXDYJXLYMYSYTWCDXCXCUUCYTXCT
      VGUUAXIYKXKYLYTYSWJEXHXHUUDYSXHTVHUUAWJEXJUUBVKVJVEVIVIVJVEVLVMVN $.
      $( [8-Sep-2014] $)

    dfmvzpolyf1 $p |- ( N e. NN0 -> ( MVZPolyF ` N ) = ( FRSD ` ( MVZPolyF_R ` N ) ) ) $=
      ( va cv cmvzpolyf_r cfv cfrsd cn0 cmvzpolyf wceq eqidd fveq12d df-mvzpolyf
      fveq2 fvex fvmpt ) BABCZDEZFEADEZFEGHPAIZQRFFSFJPADMKBLRFNO $.
      $( [8-Sep-2014] $)
    $}

    ${
    $d u N $.
    mvzpolyf-r-ssxp $p |- ( N e. NN0 -> ( MVZPolyF_R ` N ) C_ (
        U_ u e. NN0 ( ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) ^m ( 1 ... u ) ) X.
        ( ZZ ^m ( ZZ ^m ( 1 ... N ) ) ) ) ) $=
      ( vc vd va vb cn0 wcel cfv cz c1 cfz co cmap cv wa wceq cmpt wrex wo c0 c2
      cmvzpolyf_r ciun cxp wss cop cpr caddc copab opabssxp dfmvzpolyf-r1 sseq1d
      cmul a1i mpbird ) BGHZBUCIZAGJJKBLMZNMZNMZKAOZLMNMUDZVAUEZUFCOZVCHDOZVAHPV
      EUAQVFEUTVBEOZIRQAUSSVFEUTVBRQAJSTPVEKVBUGUBVGUGUHQVFFUTFOZVBIZVHVGIZUIMRQ
      VFFUTVIVJUNMRQTPEVASAVASTZPCDUJZVDUFZVMUQVKCDVCVAUKUOUQURVLVDCDFEABULUMUP
      $.
      $( [9-Sep-2014] $)
    $}
    mvzpolyf-r-rnss $p |- ( N e. NN0 -> ran ( MVZPolyF_R ` N ) C_ ( ZZ ^m
        ( ZZ ^m ( 1 ... N ) ) ) ) $=
      ( va cn0 wcel cmvzpolyf_r cfv cz c1 cfz co cmap cv cxp wss mvzpolyf-r-ssxp
      ciun crn rnss c0 cc0 wceq 0nn0 ovex elmapfz0 elmapeliunmap mp2an ne0i rnxp
      wne mp2b sseq2i biimpi 3syl ) ACDAEFZBCGGHAIJKJZKJZHBLIJKJPZUPMZNUNQZURQZN
      ZUSUPNZBAOUNURRVAVBUTUPUSSUQDZUQSUIUTUPUATCDSUPHTIJKJDVCUBUPGUOKUCZUDBTSUP
      VDUEUFUQSUGUQUPUHUJUKULUM $.
      $( [9-Sep-2014] $)
    elmvzpolyfelmap0 $p |- ( ( A e. NN0 /\ B e. ( FRSD ` ( MVZPolyF_R `
        A ) ) ) -> B e. ( ZZ ^m ( ZZ ^m ( 1 ... A ) ) ) ) $=
      ( cn0 wcel cmvzpolyf_r cfv cfrsd wa cz cfz cmap crn wss cvv fvex frsd-ssrn
      c1 co ax-mp a1i mvzpolyf-r-rnss adantr sstrd simpr sseldd ) ACDZBAEFZGFZDZ
      HZUHIIQAJRKRKRZBUJUHUGLZUKUHULMZUJUGNDUMAEOUGPSTUFULUKMUIAUAUBUCUFUIUDUE
      $.
      $( [9-Sep-2014] $)
    mvzpolyfssmap $p |- ( N e. NN0 -> ( MVZPolyF ` N ) C_ ( ZZ ^m ( ZZ ^m
        ( 1 ... N ) ) ) ) $=
      ( cn0 wcel cmvzpolyf cfv cmvzpolyf_r crn cz c1 cfz co cmap dfmvzpolyf1 wss
      cfrsd cvv fvex frsd-ssrn ax-mp a1i eqsstrd mvzpolyf-r-rnss sstrd ) ABCZADE
      ZAFEZGZHHIAJKLKLKUDUEUFOEZUGAMUHUGNZUDUFPCUIAFQUFRSTUAAUBUC $.
      $( [9-Sep-2014] $)

    $( mapfz0 and an easy way to get from map to unimap would help here a bit.  there's still a lot of apparently irreducible tedium $)
    $( what else might help are quick bound variable changers and a short notation for tuples $)
    ${
    $d x A $.  $d x B $.  $d x C $.
    const-mvzpolyf $p |- ( ( A e. NN0 /\ B e. ZZ ) -> ( x e. ( ZZ ^m ( 1 ... A ) ) |-> B ) e. ( MVZPolyF ` A ) ) $=
      ( vb va vc wcel cz wa c1 co cmap cmpt cfv cc0 c0 cv wceq wrex eqidd cn0 wf
      cfz cmvzpolyf_r cfrsd cmvzpolyf cvv wbr simplr eqid fmptd zex elmap sylibr
      ovex elex syl 0nn0 jctil fvex elmapfz0 a1i ciun wo cop c2 caddc cmul simpl
      cpr wb 0ex dfmvzpolyf-r2 syl3anc elmapeliunmap mp2an mpteq12dv weq cbvmptv
      simpr id syl6eq eqeq2d rcla4ev syl2anc olcd jca orcd mpbir2and dfmvzpolyf1
      frsd-con adantr eleqtrrd ) BUAGZCHGZIZAHJBUCKZLKZCMZBUDNZUENZBUFNZWPOUAGZW
      SUGGZIPXAJOUCKZLKGZPWSWTUHZWSXAGWPXDXCWPWSHWRLKZGZXDWPWRHWSUBXIWPAWRCHWSWN
      WOAQWRGUIWSUJUKHWRWSULHWQLUOUMUNZWSXHUPUQZURUSXFWPXAWTUEUTVAVBWPXGPDUAXHJD
      QZUCKLKVCGZXIIZPPRZWSEWRXLEQZNMRDWQSZWSEWRXLMZRZDHSZVDZIZPJXLVEVFXPVEVJRWS
      FWRFQZXLNZYCXPNZVGKMRWSFWRYDYEVHKMRVDIEXHSDXHSZVDZWPWNPUGGZXDXGXNYGIVKWNWO
      VIYHWPVLVBXKFEDPWSBVMVNWPXIXMXJXCPXHXELKGXMURXHHWRLUOZVADOPXHYIVOVPUSWPYBY
      FWPXOYAWPPTWPXTXQWPWOWSWSRZXTWNWOVTWPWSTXSYJDCHXLCRZXRWSWSYKXREWRCMWSYKEWR
      XLWRCYKWRTYKWAVQEAWRCCEAVRCTVSWBWCWDWEWFWGWHWIOPWSWTBUDUTWKVNWNXBXARWOBWJW
      LWM $.
      $( [8-Sep-2014] $)

    proj-mvzpolyf $p |- ( ( A e. NN0 /\ B e. ( 1 ... A ) ) -> ( x e. ( ZZ ^m ( 1 ... A ) ) |-> ( x ` B ) ) e. ( MVZPolyF ` A ) ) $=
      ( va vb vc wcel c1 cfz co wa cz cmap cv cfv cmpt cc0 c0 wceq wrex cfrsd wf
      cn0 cmvzpolyf_r cmvzpolyf cvv wbr simpr simplr ovex zex mapfv syl2anc eqid
      fmptd elmap sylibr elex syl 0nn0 jctil fvex elmapfz0 a1i ciun wo cop caddc
      c2 cpr cmul wb simpl dfmvzpolyf-r2 syl3anc elmapeliunmap mp2an eqidd fveq2
      0ex mpteq12dv fveq1 cbvmptv syl6eq eqeq2d rcla4ev eqid1 mpbir2and frsd-con
      orcd dfmvzpolyf1 adantr eleqtrrd ) BUCGZCHBIJZGZKZALWOMJZCANZOZPZBUDOZUAOZ
      BUEOZWQQUCGZXAUFGZKRXCHQIJZMJGZRXAXBUGZXAXCGWQXFXEWQXALWRMJZGZXFWQWRLXAUBX
      KWQAWRWTLXAWQWSWRGZKXLWPWTLGWQXLUHWNWPXLUILWSWOCHBIUJUKULUMXAUNUOLWRXAUKLW
      OMUJUPUQZXAXJURUSZUTVAXHWQXCXBUAVBVCVDWQXIRDUCXJHDNZIJMJVEGZXKKZRRSZXAEWRX
      OENZOZPZSZDWOTZXAEWRXOPSDLTZVFZKZRHXOVGVIXSVGVJSXAFWRFNZXOOZYGXSOZVHJPSXAF
      WRYHYIVKJPSVFKEXJTDXJTZVFZWQWNRUFGZXFXIXQYKKVLWNWPVMYLWQVTVDXNFEDRXABVNVOW
      QXKXPXMXERXJXGMJGXPUTXJLWRMUJZVCDQRXJYMVPVQVAWQYFYJWQYEXRWQYCYDWQWPXAXASZY
      CWNWPUHWQXAVRYBYNDCWOXOCSZYAXAXAYOYAEWRCXSOZPXAYOEWRXTWRYPYOWRVRXOCXSVSWAE
      AWRYPWTCXSWSWBWCWDWEWFUMWJRWGVAWJWHQRXAXBBUDVBWIVOWNXDXCSWPBWKWLWM $.
      $( [9-Sep-2014] $)

    sum-mvzpolyf $p |- ( ( A e. NN0 /\ B e. ( MVZPolyF ` A ) /\ C e. ( MVZPolyF ` A ) ) -> ( x e. ( ZZ ^m ( 1 ... A ) ) |-> ( ( B ` x ) + ( C ` x ) ) ) e. ( MVZPolyF ` A ) ) $=
      ( va vb vc wcel cfv cz c1 co cmap caddc cmpt c2 wa wceq wo eqeq2d cv cfrsd
      cn0 cmvzpolyf cfz cmvzpolyf_r w3a cvv cop cpr wbr 2nn0 a1i ovex mptex fvex
      wi elmapfz2 3adant1 ciun c0 elmvzpolyfelmap0 3adant3 3adant2 elmapeliunmap
      wrex cmul syl2anc wf simp1 zex mapfv 3ad2antl2 3ad2antl3 zaddcl ex syl3anc
      imp eqid fmptd elmap sylibr eqidd fveq2 oveq12d cbvmptv opeq2 preq1d fveq1
      weq orcd oveq1d mpteq12dv orbi12d anbi12d preq2d oveq2d rcla42ev syl112anc
      olcd jca31 prex dfmvzpolyf-r2 mpbird frsd-con syl211anc dfmvzpolyf1 eleq2d
      wb 3exp imbi12d 3imtr4d 3imp ) BUCHZCBUDIZHZDXOHZAJKBUELZMLZAUAZCIZXTDIZNL
      ZOZXOHZXNCBUFIZUBIZHZDYGHZYDYGHZUQXPXQYEUQXNYHYIYJXNYHYIUGZPUCHZYDUHHZKCUI
      ZPDUIZUJZYGKPUELZMLHZYPYDYFUKZYJYLYKULUMZYMYKAXSYCJXRMUNZUOUMZYHYIYRXNCDYG
      YFUBUPURUSYKYSYPEUCJXSMLZKEUAZUELMLUTHZYDUUCHZQYPVARYDFXSUUDFUAZIOREXRVFYD
      FXSUUDOREJVFSQZYPKUUDUIZPUUGUIZUJZRZYDGXSGUAZUUDIZUUMUUGIZNLZOZRZYDGXSUUNU
      UOVGLZOZRZSZQZFUUCVFEUUCVFZSZQZYKUUEUUFUVEYKYLYPUUCYQMLHZUUEYTYKCUUCHZDUUC
      HZUVGXNYHUVHYIBCVBVCZXNYIUVIYHBDVBVDZCDUUCJXSMUNZURVHEPYPUUCUVLVEVHYKXSJYD
      VIUUFYKAXSYCJYDYKXTXSHZYCJHZYKXNUVHUVIUVMUVNUQXNYHYIVJZUVJUVKXNUVHUVIUGZUV
      MUVNUVPUVMQYAJHZYBJHZUVNUVHXNUVMUVQUVIJCXSXTUUAVKVLVMUVIXNUVMUVRUVHJDXSXTU
      UAVKVLVNYAYBVOVHVPVQVRYDVSVTJXSYDVKUUAWAWBYKUVDUUHYKUVHUVIYPYPRZYDGXSUUMCI
      ZUUMDIZNLZOZRZYDGXSUVTUWAVGLZOZRZSZUVDUVJUVKYKYPWCYKUWDUWGUWDYKAGXSYCUWBAG
      WJYAUVTYBUWANXTUUMCWDXTUUMDWDWEWFUMWKUVCUVSUWHQYPYNUUJUJZRZYDGXSUVTUUONLZO
      ZRZYDGXSUVTUUOVGLZOZRZSZQEFCDUUCUUCUUDCRZUULUWJUVBUWQUWRUUKUWIYPUWRUUIYNUU
      JUUDCKWGWHTUWRUURUWMUVAUWPUWRUUQUWLYDUWRGXSUUPXSUWKUWRXSWCZUWRUUNUVTUUONUU
      MUUDCWIZWLWMTUWRUUTUWOYDUWRGXSUUSXSUWNUWSUWRUUNUVTUUOVGUWTWLWMTWNWOUUGDRZU
      WJUVSUWQUWHUXAUWIYPYPUXAUUJYOYNUUGDPWGWPTUXAUWMUWDUWPUWGUXAUWLUWCYDUXAGXSU
      WKXSUWBUXAXSWCZUXAUUOUWAUVTNUUMUUGDWIZWQWMTUXAUWOUWFYDUXAGXSUWNXSUWEUXBUXA
      UUOUWAUVTVGUXCWQWMTWNWOWRWSWTXAYKXNYPUHHZYMYSUVFXIUVOUXDYKYNYOXBUMUUBGFEYP
      YDBXCVQXDPYPYDYFBUFUPXEXFXJXNXOYGCBXGZXHXNXQYIYEYJXNXOYGDUXEXHXNXOYGYDUXEX
      HXKXLXM $.
      $( [9-Sep-2014] $)

    mul-mvzpolyf $p |- ( ( A e. NN0 /\ B e. ( MVZPolyF ` A ) /\ C e. ( MVZPolyF ` A ) ) -> ( x e. ( ZZ ^m ( 1 ... A ) ) |-> ( ( B ` x ) x. ( C ` x ) ) ) e. ( MVZPolyF ` A ) ) $=
      ( va vb vc wcel cfv cz c1 co cmap cmul cmpt c2 a1i wa wceq eqeq2d cv cfrsd
      cn0 cmvzpolyf cfz cmvzpolyf_r w3a cvv cop cpr wbr 2nn0 ovex mptex elmapfz2
      wi fvex 3adant1 c0 wo caddc elmvzpolyfelmap0 3adant3 3adant2 elmapeliunmap
      ciun wrex syl2anc wf simp1 zex mapfv 3ad2antl2 3ad2antl3 zmulcl ex syl3anc
      imp eqid fmptd elmap sylibr eqid1 fveq2 oveq12d cbvmptv opeq2 preq1d eqidd
      weq olcd oveq1d mpteq12dv orbi12d anbi12d preq2d oveq2d rcla42ev syl112anc
      fveq1 jca31 wb prex dfmvzpolyf-r2 mpbird syl211anc 3exp dfmvzpolyf1 eleq2d
      frsd-con imbi12d 3imtr4d 3imp ) BUCHZCBUDIZHZDXOHZAJKBUELZMLZAUAZCIZXTDIZN
      LZOZXOHZXNCBUFIZUBIZHZDYGHZYDYGHZUPXPXQYEUPXNYHYIYJXNYHYIUGZPUCHZYDUHHZKCU
      IZPDUIZUJZYGKPUELZMLHZYPYDYFUKZYJYLYKULQZYMYKAXSYCJXRMUMZUNQZYHYIYRXNCDYGY
      FUBUQUOURYKYSYPEUCJXSMLZKEUAZUELMLVFHZYDUUCHZRYPUSSYDFXSUUDFUAZIOSEXRVGYDF
      XSUUDOSEJVGUTRZYPKUUDUIZPUUGUIZUJZSZYDGXSGUAZUUDIZUUMUUGIZVALZOZSZYDGXSUUN
      UUONLZOZSZUTZRZFUUCVGEUUCVGZUTZRZYKUUEUUFUVEYKYLYPUUCYQMLHZUUEYTYKCUUCHZDU
      UCHZUVGXNYHUVHYIBCVBVCZXNYIUVIYHBDVBVDZCDUUCJXSMUMZUOVHEPYPUUCUVLVEVHYKXSJ
      YDVIUUFYKAXSYCJYDYKXTXSHZYCJHZYKXNUVHUVIUVMUVNUPXNYHYIVJZUVJUVKXNUVHUVIUGZ
      UVMUVNUVPUVMRYAJHZYBJHZUVNUVHXNUVMUVQUVIJCXSXTUUAVKVLVMUVIXNUVMUVRUVHJDXSX
      TUUAVKVLVNYAYBVOVHVPVQVRYDVSVTJXSYDVKUUAWAWBYKUVDUUHYKUVHUVIYPYPSZYDGXSUUM
      CIZUUMDIZVALZOZSZYDGXSUVTUWANLZOZSZUTZUVDUVJUVKUVSYKYPWCQYKUWGUWDUWGYKAGXS
      YCUWEAGWJYAUVTYBUWANXTUUMCWDXTUUMDWDWEWFQWKUVCUVSUWHRYPYNUUJUJZSZYDGXSUVTU
      UOVALZOZSZYDGXSUVTUUONLZOZSZUTZREFCDUUCUUCUUDCSZUULUWJUVBUWQUWRUUKUWIYPUWR
      UUIYNUUJUUDCKWGWHTUWRUURUWMUVAUWPUWRUUQUWLYDUWRGXSUUPXSUWKUWRXSWIZUWRUUNUV
      TUUOVAUUMUUDCWTZWLWMTUWRUUTUWOYDUWRGXSUUSXSUWNUWSUWRUUNUVTUUONUWTWLWMTWNWO
      UUGDSZUWJUVSUWQUWHUXAUWIYPYPUXAUUJYOYNUUGDPWGWPTUXAUWMUWDUWPUWGUXAUWLUWCYD
      UXAGXSUWKXSUWBUXAXSWIZUXAUUOUWAUVTVAUUMUUGDWTZWQWMTUXAUWOUWFYDUXAGXSUWNXSU
      WEUXBUXAUUOUWAUVTNUXCWQWMTWNWOWRWSWKXAYKXNYPUHHZYMYSUVFXBUVOUXDYKYNYOXCQUU
      BGFEYPYDBXDVQXEPYPYDYFBUFUQXJXFXGXNXOYGCBXHZXIXNXQYIYEYJXNXOYGDUXEXIXNXOYG
      YDUXEXIXKXLXM $.
      $( [9-Sep-2014] $)
    $}

    ${
    $d x y u v C $.
    $d x y u v N $.
    $d ph u $. $d ph v $. $d ph y $.
    mvzpolyf-inddc.1 $e |- ( ( ph /\ y e. ZZ ) -> ( x e. ( ZZ ^m ( 1 ... N ) ) |-> y ) e. C ) $.
    mvzpolyf-inddc.2 $e |- ( ( ph /\ y e. ( 1 ... N ) ) -> ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( x ` y ) ) e. C ) $.
    mvzpolyf-inddc.3 $e |- ( ( ph /\ u e. C /\ v e. C ) -> ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` x ) + ( v ` x ) ) ) e. C ) $.
    mvzpolyf-inddc.4 $e |- ( ( ph /\ u e. C /\ v e. C ) -> ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` x ) x. ( v ` x ) ) ) e. C ) $.
    mvzpolyf-inddc $p |- ( ( N e. NN0 /\ ph ) -> ( MVZPolyF ` N ) C_ C ) $=
      ( vd wcel wa cfv c1 co wi cmpt c2 vb vc va ve vf cn0 cmvzpolyf cmvzpolyf_r
      vg cfrsd wceq dfmvzpolyf1 adantr cz cfz cmap cin cvv wbr wral wss fvex a1i
      cv ovex inex2 ciun c0 wrex wo cop cpr caddc wb simpl dfmvzpolyf-r2 syl3anc
      cmul vex ad2antrr fveq1 cbvmptv simpllr eleq1 anbi2d eqidd fveq2 mpteq12dv
      weq eleq1d imbi12d chvarv sylancom syl5eqelr eleq1a rexlimdva jaod adantld
      syl oveq2 oveq2d cbviunv eleq2i anbi1i ad3antrrr anass1rs simpr simplr w3a
      id wf wfn crn 1ne2 1nn0 2nn0 fnprg mp3an fneq1 3ad2ant2 mpbiri elmap inss1
      wne frn syl6ss sylanbrc fveq1d elexi ax-mp syl6req ffvelrn sylancl eqeltrd
      oveq12d eqeq2i oveq1d ex syl5bi expimpd sylbi df-f simp2 fvpr1 prid1 fvpr2
      prid2 jca syl2anc simpld simprd 3anbi2d 3anbi3d rexlimdvva sylan2b simplrr
      3ad2ant1 elin adantrr sylbid ralrimivva ralrimiva frsd-indcdd imp syl21anc
      syld eqsstrd ) GUFMZANZGUGOZGUHOZUJOZFUVHUVJUVLUKAGULUMUVIUVLFUNUNPGUOQZUP
      QZUPQZUQZFUVIUVKURMZUVPURMZUAVDZUBVDZUVKUSZUVTUVPMZRZUBURUTUAUVPPUCVDZUOQZ
      UPQZUTZUCUFUTZUVLUVPVAZUVQUVIGUHVBVCUVRUVIUVOFUNUVNUPVEVFZVCUVIUWGUCUFUVIU
      WDUFMZNZUWCUAUBUWFURUWLUVSUWFMZUVTURMZNZNUWAUVSLUFUVOPLVDZUOQZUPQZVGZMZUVT
      UVOMZNZUVSVHUKZUVTUDUVNUWPUDVDZOZSZUKZLUVMVIZUVTUDUVNUWPSZUKZLUNVIZVJZNZUV
      SPUWPVKTUXDVKVLZUKZUVTUEUVNUEVDZUWPOZUXPUXDOZVMQZSZUKZUVTUEUVNUXQUXRVRQZSZ
      UKZVJZNZUDUVOVILUVOVIZVJZNZUWBUVIUWAUYIVNZUWKUWOUVIUVHUVSURMZUWNUYJUVHAVOU
      YKUVIUAVSVCUWNUVIUBVSVCUEUDLUVSUVTGVPVQVTUWLUWMUYIUWBRUWNUWLUWMNZUXBUYHUWB
      UYLUXBNZUYHUVTFMZUWBUYMUXMUYNUYGUYMUXLUYNUXCUWLUXLUYNRUWMUXBUWLUXHUYNUXKUW
      LUXGUYNLUVMUWLUWPUVMMZNZUXFFMUXGUYNRUYPUXFBUVNUWPBVDZOZSZFBUDUVNUYRUXEUWPU
      YQUXDWAWBUWLUYOAUYSFMZUVHAUWKUYOWCACVDZUVMMZNZBUVNVUAUYQOZSZFMZRAUYONZUYTR
      CLCLWIZVUCVUGVUFUYTVUHVUBUYOAVUAUWPUVMWDWEVUHVUEUYSFVUHBUVNVUDUVNUYRVUHUVN
      WFZVUAUWPUYQWGWHWJWKIWLWMWNUXFFUVTWOWSWPUWLUXJUYNLUNUWLUWPUNMZNZUXIFMUXJUY
      NRVUKUXIBUVNUWPSZFBUDUVNUWPUWPBUDWIUWPWFWBUWLVUJAVULFMZUVHAUWKVUJWCAVUAUNM
      ZNZBUVNVUASZFMZRAVUJNZVUMRCLVUHVUOVURVUQVUMVUHVUNVUJAVUAUWPUNWDWEVUHVUPVUL
      FVUHBUVNVUAUVNUWPVUIVUHXJWHWJWKHWLWMWNUXIFUVTWOWSWPWQVTWRUXBUYLUVSUIUFUVOP
      UIVDZUOQZUPQZVGZMZUXANZUYGUYNRUWTVVCUXAUWSVVBUVSLUIUFUWRVVALUIWIUWQVUTUVOU
      PUWPVUSPUOWTXAXBXCXDUYLVVDNZUYFUYNLUDUVOUVOVVEUWPUVOMUXDUVOMNZNZUXOUYEUYNV
      VGUXONZAUWPFMZUXDFMZUYEUYNRUYLAVVDVVFUXOUVHAUWKUWMWCXEVVHVVIVVJVVHUWMUXOUW
      KVVIVVJNZVVEUXOVVFUWMUWLUWMVVDUXOVVFNWCXFVVGUXOXGUYLUWKVVDVVFUXOUVIUWKUWMX
      HXEUWMUXOUWKXIZPTVLZFUVSXKZUXOVVKVVLUVSVVMXLZUVSXMZFVAZVVNVVLVVOUXNVVMXLZP
      TYDZPUFMTUFMVVRXNXOXPPTUWPUXDUFUFXQXRUXOUWMVVOVVRVNUWKVVMUVSUXNXSXTYAUWMUX
      OVVQUWKUWMUWEUVPUVSXKZVVQUVPUWEUVSUWJPUWDUOVEYBVVTVVPUVPFUWEUVPUVSYEFUVOYC
      ZYFUUAUUQVVMFUVSUUBYGUWMUXOUWKUUCVVNUXONZVVIVVJVWBUWPPUVSOZFVWBVWCPUXNOZUW
      PVWBPUVSUXNVVNUXOXGZYHVVSVWDUWPUKXNPTUWPUXDPUFXOYIZLVSUUDYJYKVWBVVNPVVMMVW
      CFMVVNUXOVOZPTVWFUUEVVMFPUVSYLYMYNVWBUXDTUVSOZFVWBVWHTUXNOZUXDVWBTUVSUXNVW
      EYHVVSVWIUXDUKXNPTUWPUXDTUFXPYIZUDVSUUFYJYKVWBVVNTVVMMVWHFMVWGPTVWJUUGVVMF
      TUVSYLYMYNUUHUUIVQZUUJVVHVVIVVJVWKUUKAVVIVVJXIZUYAUYNUYDUYAUVTBUVNUYQUWPOZ
      UYQUXDOZVMQZSZUKZVWLUYNUXTVWPUVTUEBUVNUXSVWOUEBWIZUXQVWMUXRVWNVMUXPUYQUWPW
      GZUXPUYQUXDWGZYOWBYPVWLVWQUYNVWLVWQNUVTVWPFVWLVWQXGVWLVWPFMZVWQAEVDZFMZVVJ
      XIZBUVNUYQVXBOZVWNVMQZSZFMZRZVWLVXARELELWIZVXDVWLVXHVXAVXJVXCVVIAVVJVXBUWP
      FWDUULZVXJVXGVWPFVXJBUVNVXFUVNVWOVXJUVNWFZVXJVXEVWMVWNVMUYQVXBUWPWAZYQWHWJ
      WKAVXCDVDZFMZXIZBUVNVXEUYQVXNOZVMQZSZFMZRVXIDUDDUDWIZVXPVXDVXTVXHVYAVXOVVJ
      AVXCVXNUXDFWDUUMZVYAVXSVXGFVYABUVNVXRUVNVXFVYAUVNWFZVYAVXQVWNVXEVMUYQVXNUX
      DWAZXAWHWJWKJWLWLUMYNYRYSUYDUVTBUVNVWMVWNVRQZSZUKZVWLUYNUYCVYFUVTUEBUVNUYB
      VYEVWRUXQVWMUXRVWNVRVWSVWTYOWBYPVWLVYGUYNVWLVYGNUVTVYFFVWLVYGXGVWLVYFFMZVY
      GVXDBUVNVXEVWNVRQZSZFMZRZVWLVYHRELVXJVXDVWLVYKVYHVXKVXJVYJVYFFVXJBUVNVYIUV
      NVYEVXLVXJVXEVWMVWNVRVXMYQWHWJWKVXPBUVNVXEVXQVRQZSZFMZRVYLDUDVYAVXPVXDVYOV
      YKVYBVYAVYNVYJFVYABUVNVYMUVNVYIVYCVYAVXQVWNVXEVRVYDXAWHWJWKKWLWLUMYNYRYSWQ
      VQYTUUNUUOWQUYMUYNUWBUYMUYNNUYNUXAUWBUYMUYNXGUYLUWTUXAUYNUUPUVTFUVOUURYGYR
      UVFYTUUSUUTUVAUVBUVQUVRNUWHUWIUCUAUBUVPUVKUVCUVDUVEVWAYFUVG $.
      $( [9-Sep-2014] $)
    $}

    ${
    $d x u v z $.  $d ph u v $.  $d ps u v x $.  $d ch z $.  $d th z $.  $d ta z $.  $d et z $.  $d ze z $.  $d si z $.  $d rh z $.
    $d N u v x z $. $d A z $.
    mvzpolyf-indd.1 $e |- ( z = A -> ( ps <-> ch ) ) $.
    mvzpolyf-indd.2 $e |- ( z = u -> ( ps <-> th ) ) $.
    mvzpolyf-indd.3 $e |- ( z = v -> ( ps <-> ta ) ) $.
    mvzpolyf-indd.4 $e |- ( z = ( x e. ( ZZ ^m ( 1 ... N ) ) |-> u ) -> ( ps <-> et ) ) $.
    mvzpolyf-indd.5 $e |- ( z = ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( x ` u ) ) -> ( ps <-> ze ) ) $.
    mvzpolyf-indd.6 $e |- ( z = ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` x ) + ( v ` x ) ) ) -> ( ps <-> si ) ) $.
    mvzpolyf-indd.7 $e |- ( z = ( x e. ( ZZ ^m ( 1 ... N ) ) |-> ( ( u ` x ) x. ( v ` x ) ) ) -> ( ps <-> rh ) ) $.
    mvzpolyf-indd.8 $e |- ( ( ph /\ u e. ZZ ) -> et ) $.
    mvzpolyf-indd.9 $e |- ( ( ph /\ u e. ( 1 ... N ) ) -> ze ) $.
    mvzpolyf-indd.10 $e |- ( ( ph /\ ( u e. ( MVZPolyF ` N ) /\ th ) /\ ( v e. ( MVZPolyF ` N ) /\ ta ) ) -> ( si /\ rh ) ) $.

    mvzpolyf-indd $p |- ( ( ph /\ N e. NN0 /\ A e. ( MVZPolyF ` N ) ) -> ch ) $=
      ( va cn0 wcel cmvzpolyf cfv w3a crab wa wss cv cz c1 co cmap cmpt wi eleq1
      cfz weq anbi2d eqidd mpteq12dv eleq1d imbi12d const-mvzpolyf adantll elrab
      id adantlr sylanbrc chvarv fveq2 proj-mvzpolyf caddc simp1r sseli 3ad2ant2
      ssrab2 3ad2ant3 sum-mvzpolyf simp1l biimpi simpld cmul mul-mvzpolyf simprd
      syl3anc mvzpolyf-inddc anabss7 sseld 3impia sylib ) AOUGUHZNOUIUJZUHZUKZWT
      CXANBKWSULZUHZWTCUMAWRWTXCAWRUMZWSXBNAWRWSXBUNXDJUFLMXBOXDMUOZUPUHZUMZJUPU
      QOVCURZUSURZXEUTZXBUHZVAXDUFUOZUPUHZUMZJXIXLUTZXBUHZVAMUFMUFVDZXGXNXKXPXQX
      FXMXDXEXLUPVBVEXQXJXOXBXQJXIXEXIXLXQXIVFZXQVMVGVHVIXGXJWSUHZFXKWRXFXSAJOXE
      VJVKAXFFWRUCVNBFKXJWSSVLVOVPXDXEXHUHZUMZJXIXEJUOZUJZUTZXBUHZVAXDXLXHUHZUMZ
      JXIXLYBUJZUTZXBUHZVAMUFXQYAYGYEYJXQXTYFXDXEXLXHVBVEXQYDYIXBXQJXIYCXIYHXRXE
      XLYBVQVGVHVIYAYDWSUHZGYEWRXTYKAJOXEVRVKAXTGWRUDVNBGKYDWSTVLVOVPXDXEXBUHZLU
      OZXBUHZUKZJXIYBXEUJZYBYMUJZVSURUTZWSUHZHYRXBUHYOWRXEWSUHZYMWSUHZYSAWRYLYNV
      TZYLXDYTYNXBWSXEBKWSWCZWAWBZYNXDUUAYLXBWSYMUUCWAWDZJOXEYMWEWLYOHIYOAYTDUMZ
      UUAEUMZHIUMAWRYLYNWFYLXDUUFYNYLUUFBDKXEWSQVLWGWBYNXDUUGYLYNUUGBEKYMWSRVLWG
      WDUEWLZWHBHKYRWSUAVLVOYOJXIYPYQWIURUTZWSUHZIUUIXBUHYOWRYTUUAUUJUUBUUDUUEJO
      XEYMWJWLYOHIUUHWKBIKUUIWSUBVLVOWMWNWOWPBCKNWSPVLWQWK $.
      $( [9-Sep-2014] $)
    $}

    $( all polynomials are dominated by 2^|x|, 2^|x| is not a polynomial $)
    $( all polynomials are primitive recursive (to be defined) under integer code NGC_Z (to be defined) $)

$}

$( ---- DIOPHANTINE ---- $)
$( Define Diophantine sets and relations.  Prove composition laws and important cases like the exponential relation. $)

$( ---- MATIJASEVIC 1 ---- $)
$( Diophantine sets are semidecidable because polynomial functions are computable. $)

$( ---- MATIJASEVIC 2 ---- $)
$( Semidecidable sets are decidable by Turing machines, which can be expressed as vectorial and thus exponential satisfaction problems and are Diophantine. $)

$( ---- MATIJASEVIC 3 ---- $)
$( Diophantine <-> Semidecidable.  There exist non-decidable diophantine sets. $)

$( TODO
    Things I've wanted.  If I still want them after I'm more familiar with the system, I'll implement/call for them
    1. Cheat sheet of "do you want to do this -> use these theorems".  tell people to take advantage of min *
    2. WRITE SOURCE with $[ $] would make my life much easier
    3. Namespaces - see separate doc
    4. How to handle similar subtrees in the PA: command to copy a subtree to a new node, either with or without syntax proofs(?).  An easy way to create new lemmas from completely proved subtrees without losing PA state would be nice.
        or, create a lemma from a part of a completely proved theorem.  that would be nice.
$)
