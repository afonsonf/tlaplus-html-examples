---------------------------- CONFIG EWD998_Template ----------------------------
CONSTANT N = 9 MAXLEVEL = 0
================================================================================

---------------------------- MODULE EWD998_Template ----------------------------

EXTENDS TLC, IOUtils, Sequences, Integers, SequencesExt, HTML

CONSTANT N, MAXLEVEL

LEVEL == TLCGet("level")

\***** Styling

TaintedColorNode == "lightgray"
TaintedColorToken == "lightgray"

ClassRingItem(number_nodes) == StringSeqToString(
    [i \in 1..number_nodes |->
        HTMLClass(".node-" \o ToString(i),<<HTMLAttribute("grid-area", "n" \o ToString(i))>>)]
, "\n")

Classes == <<
    HTMLClass(".ClassTitle", <<
        HTMLAttribute("font-size", "x-large"),
        HTMLAttribute("font-weight", "bolder"),
        HTMLAttribute("border", "0px")
    >>),
    HTMLClass(".ClassInfo", <<
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("padding", "5px"),
        HTMLAttribute("text-align", "center")
    >>),
    HTMLClass(".ClassNode", <<
        HTMLFlexCenterAttributes,
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("padding", "8px"),
        HTMLAttribute("flex-flow", "wrap")
    >>),
    HTMLClass(".ClassNodeTainted", <<
        HTMLAttribute("background-color", TaintedColorNode)
    >>),
    HTMLClass(".ClassNodeActive", <<
        HTMLAttribute("border-radius", "50%")
    >>),
    HTMLClass(".ClassCenterTransparentBox", <<
        HTMLFlexCenterAttributes,
        HTMLAttribute("text-align", "center"),
        HTMLAttribute("border", "0px"),
        HTMLAttribute("margin", "auto")
    >>),
    HTMLClass(".ClassToken", <<
        HTMLAttribute("border", "3px solid black"),
        HTMLAttribute("margin-top", "15px")
    >>),
    HTMLClass(".ClassTokenTainted", <<
        HTMLAttribute("background-color", TaintedColorToken)
    >>),
    HTMLClass(".ClassTokenNormal", <<
        HTMLAttribute("background-color", "white")
    >>),
    HTMLClass(".ClassTokenHidden", <<
        HTMLAttribute("visibility", "hidden")
    >>),
    ClassRingItem(N),
    HTMLClass(".ClassRing", <<
        HTMLAttribute("grid-template-areas",StringSeqToString(<<" ",
            "\".  .  n1 .  . \"",
            "\".  n2 n1 n9 . \"",
            "\"n3 n3 .  n8 n8\"",
            "\"n4 n4 .  n7 n7\"",
            "\".  n5 .  n6 . \""
        >>, "\n")),
        HTMLAttribute("align-content", "stretch"),
        HTMLAttribute("align-items", "center"),
        HTMLAttribute("grid-template-rows", "16%"),
        HTMLSize("100%","100%")
    >>)
>>

\***** Template

Info(vars) == HTMLFrame("info-layout", <<
    HTMLBox("title", <<"ClassInfo","ClassTitle">>, HTMLSize("300px", "auto"),
        << HTMLText("title", "EWD998") >>),
    HTMLBox("info", <<"ClassInfo">>, HTMLSize("300px", "auto"), <<
        HTMLText("info-legend-1", "Circle: Active, Gray: Tainted"), HTMLNewLine, HTMLNewLine,
        HTMLText("info-legend-2", "Line: Message, Arrow: Receiver"), HTMLNewLine, HTMLNewLine,
        \* HTMLText("info-legend-3", "Dashed: In-Flight, Solid: Arrival in next"), HTMLNewLine, HTMLNewLine,
        HTMLText("info-level-s", "Level: "), HTMLText("info-level-x", ToString(LEVEL))
    >>)
>>)

Node(id_i, name, vars) ==
    LET id == ToString(id_i)
        tokencounter == ToString(vars.token.q)
        nodecounter == ToString(vars.counter[id_i-1])
        nodeClassColor == IF vars.color[id_i-1] = "black" THEN "ClassNodeTainted" ELSE ""
        nodeClassShape == IF vars.active[id_i-1] THEN "ClassNodeActive" ELSE ""
        tokenClass == IF vars.token.pos = id_i-1
            THEN IF vars.token.color = "black" THEN "ClassTokenTainted" ELSE "ClassTokenNormal"
            ELSE "ClassTokenHidden"
    IN
    HTMLBox("node-container", <<"ClassCenterTransparentBox","ClassNode","node-" \o id>>, HTMLSize("100px", "100px"), <<
        HTMLBox("node-" \o id, <<nodeClassShape,nodeClassColor, "ClassNode">>, HTMLSize("80px", "80px"), <<
            HTMLBox("node-name", <<"ClassCenterTransparentBox">>, HTMLSize("100%", "20px"),<<
                HTMLText("node-name-text", name)
            >>),
            HTMLBox("node-counter", <<"ClassCenterTransparentBox">>, HTMLSize("100%", "20px"),<<
                HTMLText("node-counter-text", nodecounter)
            >>)
        >>),
        HTMLBox("node-token-container", <<"ClassCenterTransparentBox">>, HTMLSize("100%", "20px"),<<
            HTMLCircle("token", <<tokenClass, "ClassToken">>, HTMLSize("30px", "20px"),<<
                HTMLText("token-counter", tokencounter)
            >>)
        >>)
    >>)

Ring(vars) ==
    HTMLGridContainer("ring", <<"ClassRing">>,
        [i \in 1..N |-> Node(i, "Node " \o ToString(i), vars) ])

Content(vars) == HTMLFrame("content-layout", <<
    HTMLBox("grid-container", <<"ClassCenterTransparentBox">>, HTMLSize("70%", "700px"),
        <<Ring(vars)>>
    )
>>)

Page(vars) == HTMLFrame("page-layout",
    <<Info(vars), HTMLNewLine, Content(vars)>>)

\***** Script

LinesScript(vars) == HTMLScript( SetToSeq(
    { HTMLJSLine("node-" \o ToString(m.from+1),
                 "node-" \o ToString(m.dest+1),
                 "darkblue", "3")
        : m \in vars.messages } ) )

NavigationScriptListener(prev, next) ==
    HTMLJSKeyListener(<<
        HTMLJSNavigationKey("ARROWLEFT", prev \o ".html"),
        HTMLJSNavigationKey("ARROWRIGHT", next \o ".html")
    >>)

NavigationScript == HTMLScript(<<
    LET prev_page_number == IF LEVEL = 1 THEN 1 ELSE LEVEL-1
        next_page_number == IF LEVEL = MAXLEVEL THEN MAXLEVEL ELSE LEVEL+1
    IN NavigationScriptListener(
        ToString(prev_page_number), ToString(next_page_number))
>>)

\***** Template Main

Body(vars) == HTMLBody( Page(vars) )

Header == HTMLHeader("EWD998", <<>>, Classes)

Scripts(vars) == <<
    HTMLScriptFile("../../lib/leader-line.min.js"),
    LinesScript(vars),
    NavigationScript
>>

Template(vars) == HTMLDocument(Header, Body(vars), Scripts(vars))

\***** Test Template

testVars == [
    pending |-> [i \in 0..8 |-> 0],
    counter |-> ( 0 :> 0 @@ 1 :> 0  @@ 2 :> 0 @@
                  3 :> 1 @@ 4 :> -1 @@ 5 :> 1 @@
                  6 :> 0 @@ 7 :> 0  @@ 8 :> 0 ),
    token |-> [color |-> "black", pos |-> 5, q |-> 1],
    active |-> ( 0 :> TRUE  @@ 1 :> TRUE  @@ 2 :> TRUE @@
                 3 :> TRUE  @@ 4 :> FALSE @@ 5 :> TRUE @@
                 6 :> FALSE @@ 7 :> FALSE @@ 8 :> TRUE ),
    color |-> ( 0 :> "white" @@ 1 :> "black" @@ 2 :> "white" @@
                3 :> "white" @@ 4 :> "black" @@ 5 :> "black" @@
                6 :> "white" @@ 7 :> "black" @@ 8 :> "white" ),
    messages |-> {[from |-> 3, dest |-> 7]}
]

ASSUME PrintT(Serialize(Template(testVars), "html-example/test/test.html",
           [format      |-> "TXT",
            charset     |-> "UTF-8",
            openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]))

================================================================================
