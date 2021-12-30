---------------------------- CONFIG EWD998_Template ----------------------------
CONSTANT N = 9 MAXLEVEL = 0
================================================================================

---------------------------- MODULE EWD998_Template ----------------------------

EXTENDS TLC, IOUtils, Sequences, Integers, SequencesExt, HTML, SVG

CONSTANT N, MAXLEVEL

LEVEL == TLCGet("level")
Color == {"white", "black"}

\***** Styling

TaintedColorNode == "lightgray"
TaintedColorToken == "lightgray"

ClassRingItem(number_nodes) == FlattenSeq(
    [i \in 1..number_nodes |->
        HTMLClass(".node-" \o ToString(i),<<HTMLAttribute("grid-area", "n" \o ToString(i))>>)]
)

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
    HTMLClass(".ClassCenterTransparentBox", <<
        HTMLFlexCenterAttributes,
        HTMLAttribute("text-align", "center"),
        HTMLAttribute("border", "0px"),
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("font-size", "8px")
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

--------------------------------------------------------------------------------

\* Taken from https://github.com/tlaplus/Examples/blob/master/specifications/ewd998/EWD998_anim.tla

Arial == [font |-> "Arial"]
NodeDimension == 20
RingBasePos == [w |-> 55, h |-> 55, r |-> 75]
ArrowPosOffset == NodeDimension \div 2
TokenBasePos == [ w |-> RingBasePos.w + 12,
                  h |-> RingBasePos.h + 12,
                  r |-> RingBasePos.r + 25 ]

RingNetwork(vars) ==
    LET RN[ n \in 1..N ] ==
            LET coord == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, n, N)
                id == Text(coord.x + ArrowPosOffset - 2, coord.y + ArrowPosOffset + 4,
                        ToString(vars.counter[n-1]),
                        Arial @@ [fill |-> CHOOSE c \in Color : c # vars.color[n-1]])
                node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,
                            [rx |-> IF ~vars.active[n-1] THEN "0" ELSE "15",
                             stroke |-> "black",
                             fill |-> vars.color[n-1]])
            IN Group(<<node, id>>, <<>>)
    IN Group(RN, <<>>)

TokenNetwork(vars) ==
    LET coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, vars.token.pos, N)
        circ  == Circle(coord.x-2, coord.y, 5, [stroke |-> "black", fill |-> vars.token.color])
        id    == Text(coord.x - 4, coord.y + 3, ToString(vars.token.q),
                    [font |-> "Arial", fill |-> CHOOSE c \in Color : c # vars.token.color])
    IN Group(<<circ, id>>, <<>>)

Messages(vars) ==
    LET M[ m \in vars.messages ] ==
        LET from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, m.from+1, N)
            to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, m.dest+1, N)
            line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset,
                         to.x + ArrowPosOffset, to.y + ArrowPosOffset,
                         [stroke |-> "orange", stroke_dasharray |-> "0",
                          marker_end |-> "url(#arrow)"])
        IN Group(<<line>>, <<>>)
    IN Group(M, <<>>)

Defs ==
    "<defs><marker id='arrow' markerWidth='15' markerHeight='15' refX='0' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='orange' /></marker></defs>"

Animation(vars) == HTMLSVG("ring", "-50 -50 225 225", HTMLSize("100%","100%"),
    Defs \o SVGElemToString(Group(<<RingNetwork(vars), TokenNetwork(vars), Messages(vars)>>, <<>>))
)

--------------------------------------------------------------------------------

Content(vars) == HTMLFrame("content-layout", <<
    HTMLBox("grid-container", <<"ClassCenterTransparentBox">>, HTMLSize("70%", "700px"),
        <<Animation(vars)>>
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
