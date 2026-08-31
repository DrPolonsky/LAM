\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{msthesis}[2026/02/27 App State MS Thesis Style]

% Base on report class
\ProcessOptions
\LoadClass[letterpaper,12pt]{report}
\pagestyle{empty}

% Set the proper margins, which are currently 1 inch on each side.
\RequirePackage[letterpaper,lmargin=1in,rmargin=1in,tmargin=1in,bmargin=1in,footskip=.5in]{geometry}

% Allows us to easily switch between single and double spacing
\RequirePackage{setspace}

% Allows us to modify chapter headings
\RequirePackage{titlesec}

% Set the format for chapter titles to something smaller than default
\titleformat{\chapter}[block]
  {\filcenter\normalfont\normalsize\bfseries}
  {\chaptertitlename\ \thechapter :}{5pt}{\normalsize}
\titlespacing{\chapter}{0pt}{50pt}{1ex}

% TODO: Determine if we still want this. This will cause
% quotations to be shown using single spacing.
\renewenvironment{quote}
  { \begin{singlespace} \list{}{\rightmargin\leftmargin} \item\relax}
  { \endlist \end{singlespace} }


% TODO: Determine if we still want this. This will cause
% bulleted lists to be shown using single spacing, which
% seems to match the template.
\let\old@itemize\itemize
\let\endold@itemize\enditemize
\renewenvironment{itemize}
  { \old@itemize \singlespacing}
  { \endold@itemize }

% TODO: Determine if this is still needed. I think it is,
% we don't want arrays of equations to be double-spaced.
% Single spacing in equation arrays
\let\old@eqnarray\eqnarray
\let\endold@eqnarray\endeqnarray
\renewenvironment{eqnarray}
  { \begin{singlespace*} \begin{old@eqnarray} }
  { \end{old@eqnarray} \end{singlespace*} }

% Enable the fancy page style and set up the footer.
\RequirePackage{fancyhdr}
% Clear headers and footers
\fancyhf{}  
% Add the page number, centered, to the bottom of each page
\fancyfoot[C]{\thepage} 

% We do not want a line under the page header, so set the
% width to 0pt.
\renewcommand{\headrulewidth}{0pt}

% Commands to represent the information that appears
% on the signature page and in several other locations
% such as the advisor and department. 
\newcommand{\department}[1]{\gdef\@department{#1}}
\department{??DEPARTMENT??}
\newcommand{\school}[1]{\gdef\@school{#1}}
\school{}
\newcommand{\degree}[1]{\gdef\@degree{#1}}
\degree{??DEGREE??}
\newcommand{\advisor}[2]{
  \gdef\@advisor{#1\ifstrempty{#2}{}{, #2}}
  \gdef\@advisornd{#1}
}
\advisor{??ADVISOR??}{??DEGREE??}
\newcommand{\thesismonth}[1]{\gdef\@thesismonth{#1}}
\newcommand{\thesisyear}[1]{\gdef\@thesisyear{#1}}
\newcommand{\copyrightyear}[1]{\gdef\@copyrightyear{#1}}
\copyrightyear{\@thesisyear}

% TODO: Add this back in if needed. We would also need
% logic where it is used to handle cases where it does
% not appear.
% \newcommand{\program}[1]{\gdef\@program{#1}}
% \department{??PROGRAM??}

% A preliminary chapter (although this is also used for the
% vita at the end). This is a chapter that should not be
% assigned a chapter number, like the dedication or the vita.
% We ensure it still shows up in the table of contents.
\newcommand{\pchapter}[1] { %% A preliminary chapter
  \chapter*{#1}
  \addcontentsline{toc}{chapter}{#1}
}

% Special environment for the acknowledgements page at the
% start of the thesis.
\newenvironment{acknowledgements}{
    \thispagestyle{fancy}
    \normalbaselines
    \pchapter{Acknowledgments}
    % \vspace{-7ex}
    \doublespacing
}{
    \clearpage
}

% Special environment for the dedication page at the
% start of the thesis.
\newenvironment{dedication}{
    \thispagestyle{fancy}
    \normalbaselines
    \pchapter{Dedication}
    % \vspace{-7ex}
    \doublespacing
}{
\clearpage
}

% Special environment for the vita page at the
% end of the thesis.
\newenvironment{vita}{
    \thispagestyle{fancy}
    \normalbaselines
    \pchapter{Vita}
    \doublespacing
}{
\clearpage
}

% Blank cover sheet. Use this if you need to force a blank
% page with no page number.
\newcommand{\coversheet}{ 
  \clearpage
  \thispagestyle{empty}
  \ 
  \clearpage }

% Member stuff based on the ECU CS thesis class, which
% was originally based on the dukethesis.cls file, modified
% to match the format used at Appalachian State University.

% \@member{member name} -- internal macro to print a line to sign on, and the
%       name of a committee member and committee member's title/role below the line.
\newcommand{\@member}[2]{
  \rule{3.5in}{1pt}\par    % Print line.
  {#2}\par      % Print member name below.
  {#1}\par % Print the member title below their name
}

% Number of member macros defined so far.
\newcounter{@members}           

% Advisor is always 1st member, so make them "member a"
\newcommand{\@membera}{\@member{Chairperson, Thesis Committee}{\@advisor}}
\setcounter{@members}{1}        


% \member{member name} -- user macro to declare the name of a committee member.
%       May be used up to 7 times.  Should not be used for advisor.
\newcommand{\member}[2][Member, Thesis Committee]{
  \addtocounter{@members}{1}    % Inc. num of members to include this new one.
  \ifcase\value{@members} 
    \typeout{Thesis format internal error.  Too few committee members.} \or
    \typeout{Thesis format internal error.  Advisor left off committee.} \or
    \newcommand{\@memberb}{\@member{#1}{#2}} \or
    \newcommand{\@memberc}{\@member{#1}{#2}} \or
    \newcommand{\@memberd}{\@member{#1}{#2}} \or
    \newcommand{\@membere}{\@member{#1}{#2}} \or
    \newcommand{\@memberf}{\@member{#1}{#2}} \or
    \newcommand{\@memberg}{\@member{#1}{#2}} \or
    \newcommand{\@memberh}{\@member{#1}{#2}} 
  \else
    \typeout{Error using thesis format.  Too many committee members.}
  \fi
}

% The chair of the department is also a member. The title is
% added automatically.
\newcommand{\departmentchair}[1] {
  \member[Chairperson, Department of \@department]{#1}
}

% The dean of the graduate school is also a member. The title
% is the second parameter, since the title may change. The
% alternative would be to hardcode it here, but then it would
% need to be updated when the title changes. An example is
% interim Dean versus just Dean.
\newcommand{\gradschool}[2] {
  \member[#2, Cratis D. Williams School of Graduate Studies]{#1}
}

% Create the title page. This is page 1, but the page number
% is not visible. It will be a roman numeral in the TOC.
\renewcommand{\maketitle}{
  \clearpage
    \thispagestyle{empty} 
    \setcounter{page}{1} 
    \pagenumbering{roman}
    \singlespacing

    \rule{0 pt}{1in}

    \begin{center}


      \MakeUppercase{\@title}

    \vskip 1in

      A Thesis \\
      by \\
      \MakeUppercase{\@author} \\

    \vskip 1.5in

      Submitted to the School of Graduate Studies \\
      at Appalachian State University \\
      in partial fulfillment of the requirements for the degree of \\
      \MakeUppercase{\@degree} \\

    \vskip 1.5in

      \@thesismonth\ \@thesisyear \\
      Department of \@department \\
    \end{center}
    
  \clearpage
}


% Create the copyright page. This will come after the
% signature page.
\newcommand{\makecopyright}{
  \clearpage
    \thispagestyle{empty}
    \singlespacing
    \rule{0 pt}{4in}

    \begin{center}
      Copyright by \@author\ \@copyrightyear \\
      All Rights Reserved
    \end{center}
  
    \vfill
  \clearpage
}

% Keep track of how many members we have printed on
% the signature page.
\newcounter{@membersprinted}

% Create the signature page.
\newcommand{\makesignature}{
  \clearpage
    \thispagestyle{empty}

    % Note: parskip is inside braces so it reverts
    % back to normal after this is done.
    {
      \setlength{\parskip}{0.05in}
    \singlespacing

    \begin{center}

    % \vspace*{\fill}

      \MakeUppercase{\@title}

    \vskip 0.75in

      A Thesis \\
      by \\
      \MakeUppercase{\@author} \\
      \@thesismonth\ \@thesisyear
    \end{center}

    \vskip .4in

    \MakeUppercase{Approved By:}

    % Print each of the committee members, including the advisor,
    % the department chair, and the dean.
	  \setcounter{@membersprinted}{0}%
	  \@whilenum \value{@membersprinted} < \value{@members} \do {%
            \stepcounter{@membersprinted}%
            \vskip .4in
            \ifcase\value{@membersprinted}%
              \typeout{Thesis style--internal error printing members.} \or%
              \@membera \or%
              \@memberb \or%
              \@memberc \or%
              \@memberd \or%
              \@membere \or%
              \@memberf \or%
              \@memberg \or%
              \@memberh%
            \else \typeout{Thesis style--internal error printing members.}%
            \fi %
          }%
    }
  \clearpage
}

% Set up the table of contents format
\RequirePackage[titles]{tocloft}
\RequirePackage{etoolbox}

\tocloftpagestyle{empty}

\renewcommand{\cftchapdotsep}{\cftdotsep}
\renewcommand{\cftchappresnum}{} 
\renewcommand{\cftchappagefont}{}
\renewcommand{\cftchapfont}{}
\setcounter{tocdepth}{4}

% Create the Table of Contents page.
\renewcommand{\contentsname}{Table of Contents}
\renewcommand{\tableofcontents}{
  \clearpage
  \thispagestyle{empty}
  \normalbaselines
  \chapter*{\contentsname}
  \markboth{CONTENTS}{CONTENTS}
  \@starttoc{toc}
  \clearpage
}

% Create the List of Tables page.
\renewcommand{\listoftables}{
  \clearpage
  \thispagestyle{fancy}
  \normalbaselines
  \pchapter{List of Tables}
  \markboth{LIST OF TABLES}{LIST OF TABLES}
  \@starttoc{lot}
  \clearpage
}

% Create the List of Figures page.
\renewcommand{\listoffigures}{
  \clearpage
  \thispagestyle{fancy}
  \normalbaselines
  \pchapter{List of Figures}
  \markboth{LIST OF FIGURES}{LIST OF FIGURES}
  \@starttoc{lof}
  \clearpage
}

% Set up the Table of Contents display info for the List of Figures
% and for the List of Tables (which will have the same format).
\def\l@figure{{\protect\addvspace{14.5pt}}\@dottedtocline{1}{1.5em}{2.3em}}
\def\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\let\l@table\l@figure

% The \chapters command is used before the first regular chapter
% in the theses. This switches page numbering to arabic numerals,
% resets the page number to 1, and turns on the fancy page style
% to include page numbers on each page. It also switches to
% doublespacing since the remaining content will be double-spaced.
\newcommand{\chapters} {
  \clearpage
  \pagestyle{fancy}
  \setcounter{page}{1}
  \pagenumbering{arabic}
  \doublespacing
}

% Make the bibliography. The bibliography should be single spaced, 
% and should be placed in the table of contents.
\renewcommand{\bibname}{References}
\renewenvironment{thebibliography}[1]
     {\chapter*{\bibname}%
      \singlespacing %
      \addcontentsline{toc}{chapter}{\bibname}%
      \@mkboth{\MakeUppercase\bibname}{\MakeUppercase\bibname}%
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy
      \clubpenalty4000
      \@clubpenalty \clubpenalty
      \widowpenalty4000%
      \sfcode`\.\@m}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}

% Similar to members, define a credential as degree and institution
\newcommand{\@credential}[2]{
  {#1}, {#2} \\
}

% Keep track of added credentials.
\newcounter{@credentials}
\setcounter{@credentials}{0}

% It is possible to have up to 4 credentials.
\newcommand{\credential}[2]{
  \addtocounter{@credentials}{1}
  \ifcase\value{@credentials}
    \newcommand{\@credentiala}{\@credential{#1}{#2}} \or
    \newcommand{\@credentialb}{\@credential{#1}{#2}} \or
    \newcommand{\@credentialc}{\@credential{#1}{#2}} \or
    \newcommand{\@credentiald}{\@credential{#1}{#2}}
  \else
    \typeout{Error using thesis format.  Too many credentials members.}
  \fi
}

% For printing, keep track of how many credentials we've printed
\newcounter{@credsprinted}

% Create the abstract page. This will include the defined credentials.
\renewenvironment{abstract}{
  \clearpage
  \thispagestyle{fancy}
  \normalbaselines
  \singlespacing
  \pchapter{Abstract}
  % \vspace{-7ex}
  \begin{center}
  \MakeUppercase{\@title} \\
  \vskip .1in
  \@author \\
  
% Print credentials
	  \setcounter{@credsprinted}{0}%
	  \@whilenum \value{@credsprinted} < \value{@credentials} \do {%
            \stepcounter{@credsprinted}%
            \ifcase\value{@credsprinted}%
              \@credentiala \or%
              \@credentialb \or%
              \@credentialc \or%
              \@credentiald
            \else \typeout{Thesis style--internal error printing credentials.}%
            \fi %
          }%
  % This just makes sure we have something to print before going to the next
  % line, otherwise LaTeX doesn't like ending the line.
  \textsf{ } \\
  \textsf{ } \\
  Chairperson: \@advisornd
  \vskip .1in
  \end{center}

  \doublespacing
  \parindent0.25in
  \pagestyle{fancy}
} {
  \clearpage
}

% Create the forward.
\newenvironment{foreword}{
  \clearpage
    \pchapter{Foreword}
    \pagestyle{fancy}
    \doublespacing
}{
  \clearpage
}
