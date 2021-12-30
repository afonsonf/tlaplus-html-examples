------------------- CONFIG MissionariesAndCannibals_Template -------------------

================================================================================

------------------- MODULE MissionariesAndCannibals_Template -------------------

EXTENDS TLC, IOUtils, Sequences, Integers, HTML

LEVEL == TLCGet("level")
MAXLEVEL == TLCGet("diameter")

\***** Styling

Classes == <<
    HTMLClass(".ClassTitle", <<
        HTMLAttribute("font-size", "x-large"),
        HTMLAttribute("font-weight", "bolder"),
        HTMLAttribute("border", "0px")
    >>),
    HTMLClass(".ClassInfo", <<
        HTMLAttribute("text-align", "center"),
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("padding", "5px")
    >>),
    HTMLClass(".ClassContent", <<
        HTMLFlexCenterAttributes,
        HTMLAttribute("margin", "auto"),
        HTMLAttribute("padding", "10px")
    >>),
    HTMLClass(".ClassNode", <<
        HTMLFlexCenterAttributes,
        HTMLAttribute("margin", "10px")
    >>),
    HTMLClass(".ClassHidden", <<
        HTMLAttribute("visibility", "hidden")
    >>)
>>

\***** Template

Info(vars) == HTMLFrame("info-layout", <<
    HTMLBox("title", <<"ClassInfo","ClassTitle">>, HTMLSize("300px", "auto"),
        << HTMLText("title", "Missionaries and Cannibals") >>),
    HTMLBox("info", <<"ClassInfo">>, HTMLSize("300px", "auto"), <<
        HTMLText("info-legend", "Depth: " \o ToString(LEVEL)),
        HTMLNewLine
    >>)
>>)

Island(vars, side) ==
    HTMLBox("island" \o side, <<"ClassNode">>, HTMLSize("300px", "300px"),
        <<ToString(vars.who_is_on_bank[side] \ vars.who_moved)>>)

Boat(vars, side) ==
    LET boatClass == IF vars.bank_of_boat # side THEN "ClassHidden" ELSE ""
    IN HTMLBox("boat" \o side, <<"ClassNode", boatClass>>, HTMLSize("300px", "100px"),
        <<ToString(vars.who_moved)>>)

Content(vars) == HTMLBox("content-box", <<"ClassContent">>, HTMLSize("fit-content", "auto"),
    <<
        Island(vars, "W"), Boat(vars, "W"),
        HTMLBox("separator", <<>>, HTMLSize("1px", "250px"), <<>>),
        Boat(vars, "E"), Island(vars, "E")
    >>)

Page(vars) == HTMLFrame("page-layout",
    <<Info(vars), HTMLNewLine, Content(vars)>>)

\***** Scripts

NavigationScriptListener(prev, next) ==
    HTMLJSKeyListener(<<
        HTMLJSNavigationKey("ARROWLEFT", prev \o ".html"),
        HTMLJSNavigationKey("ARROWRIGHT", next \o ".html")
    >>)

NavigationScript ==
    HTMLScript(<<
        LET prev_page_number == IF LEVEL = 1 THEN 1 ELSE LEVEL-1
            next_page_number == IF LEVEL = MAXLEVEL THEN MAXLEVEL ELSE LEVEL+1
        IN NavigationScriptListener(
            ToString(prev_page_number), ToString(next_page_number))
    >>)

\***** Template Main

Body(vars) == HTMLBody( Page(vars) )

Header == HTMLHeader("MissionariesAndCannibals",<<>>,Classes)

Scripts == <<NavigationScript>>

Template(vars) == HTMLDocument(Header, Body(vars), Scripts)

\***** Test Template

testVars == [
    bank_of_boat |-> "E",
    who_is_on_bank |-> [E |-> {"c1", "m1", "m2", "m3"}, W |-> {"c2", "c3"}],
    who_moved |-> {"c1","m2"}
]

ASSUME PrintT(Serialize(Template(testVars), "html-example/test/test.html",
           [format      |-> "TXT",
            charset     |-> "UTF-8",
            openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]))

================================================================================
