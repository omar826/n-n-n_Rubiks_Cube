import ProofWidgets

open ProofWidgets

-- Define an HTML element
def myHtml : Html := 
  Html.div #[
    Html.text "Hello, Lean!"
  ]

-- Render the HTML
#eval myHtml
