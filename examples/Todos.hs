{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad        (forever, void)
import           Control.Monad.State  (StateT, execStateT, get, lift, put)

import           Data.List            (intersperse)
import           Data.String          (fromString)

import qualified GHCJS.VDOM.Attribute as A
import qualified GHCJS.VDOM.Element   as E
import qualified GHCJS.VDOM.Event     as Ev

import           Concur               (HTML, Widget, button, classList, clickEl,
                                       el, elT, elT_, el_, initConcur,
                                       orr, runWidgetInBody, inputEnter, text, editableText,
                                       elEvent)

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Run widget
  runWidgetInBody $ void $ flip execStateT startEntries widgetTodos


-----------------------------------------------------
-- Data Structures, and associated pure operations --
-----------------------------------------------------

data Entry = Entry
    { entryDescription :: String
    , entryCompleted   :: Bool
    }

data EntriesVisibility = All | Active | Completed
  deriving (Show, Eq)

data EntriesList = EntriesList
  { entriesVisibility :: EntriesVisibility
  , entriesList       :: [Entry]
  }

startEntries :: EntriesList
startEntries = EntriesList All []

entriesCompleted :: EntriesList -> Int
entriesCompleted = length . filter entryCompleted . entriesList

entriesLeft :: EntriesList -> Int
entriesLeft elist = length (entriesList elist) - entriesCompleted elist


-------------
-- Widgets --
-------------

type EntriesWidget a = StateT EntriesList (Widget HTML) a

widgetTodos :: EntriesWidget a
widgetTodos = forever $ elT E.div [ A.class_ "todomvc-wrapper" ]
  [ elT E.section [A.class_ "todoapp"] [widgetInput, widgetEntries, widgetControls]
  , lift $ el E.footer [ A.class_ "info" ]
        [ el E.p [] [text "Double-click to edit a todo"]
        , el E.p []
            [ text "Written by "
            , el E.a [ A.href "https://github.com/ajnsit" ] [ text "Anupam Jain" ]
            ]
        , el E.p []
            [ text "Part of "
            , el E.a [ A.href "https://todomvc.com" ] [ text "TodoMVC" ]
            ]
        ]
  ]

-- <p>Part of <a href="http://todomvc.com">TodoMVC</a></p>

widgetInput :: EntriesWidget ()
widgetInput = elT E.header
  [ A.class_ "header" ]
  [ elT E.h1 [] [lift $ text "todos"]
  , do
      elist <- get
      s <- lift $ inputEnter [A.class_ "new-todo", A.placeholder "What needs to be done?", A.autofocus "autofocus", A.name "newTodo", A.value ""] ""
      put $ elist { entriesList = Entry s False : entriesList elist }
  ]

widgetEntries :: EntriesWidget ()
widgetEntries = do
  elist <- get
  elT E.section [ classList [("main", True), ("hidden", null $ entriesList elist)] ]
    [ lift (allCompletedToggle (allCompleted elist)) >>= put . flip markAllComplete elist
    , elT_ E.ul [ A.class_ "todo-list" ] $ elistToEntriesListWidget elist
    ]
  where
    addChecked v l = if v then (A.checked "checked" : l) else l
    allCompletedToggle v = clickEl E.input (addChecked v [A.type_ "checkbox", A.class_ "toggle-all", A.name "toggle"]) (const $ not v) []
    elistToEntriesListWidget elist = orr $ map (numberedEntryToWidget elist) $ filter (isEntryVisible (entriesVisibility elist) . snd) $ zip [0..] $ entriesList elist
    numberedEntryToWidget elist (i,e) = do
      let l = entriesList elist
      me <- lift $ widgetEntry e
      put $ elist { entriesList = case me of
                      Nothing -> take i l ++ drop (i+1) l
                      Just e' -> take i l ++ [e'] ++ drop (i+1) l
                  }
    isEntryVisible Completed = entryCompleted
    isEntryVisible Active    = not . entryCompleted
    isEntryVisible All       = const True
    allCompleted elist = entriesLeft elist <= 0
    markAllComplete v elist = elist { entriesList = map (\e -> e {entryCompleted = v}) (entriesList elist) }

-- <div class="view"><input class="toggle" type="checkbox"><label>haha</label><button class="destroy"></button></div>

-- <li class=""><div class="view"><input class="toggle" type="checkbox"><label>haha</label><button class="destroy"></button></div><input class="edit" name="title" id="todo-2"></li>
widgetEntry :: Entry -> Widget HTML (Maybe Entry)
widgetEntry todo = el_ E.li [ classList [ ("completed", entryCompleted todo), ("editing", False) ] ] $
  el E.div [ A.class_ "view" ] $
    [ clickEl E.input (addChecked (entryCompleted todo) [A.type_ "checkbox", A.class_ "toggle"])
        (\_e -> Just $ todo { entryCompleted = not $ entryCompleted todo }) []
    , fmap (\desc' -> Just $ todo { entryDescription = desc' }) $ do
        elEvent Ev.dblclick E.label [] (text desc)
        inputEnter [A.class_ "edit", A.name "title"] desc
    , clickEl E.button [A.class_ "destroy"] (const Nothing) []
    ]
  where
    desc = entryDescription todo
    addChecked v l = if v then (A.checked "checked" : l) else l

widgetControls :: EntriesWidget ()
widgetControls = do
  elist <- get
  elT E.footer
      [ classList [("footer", True), ("hidden", null $ entriesList elist)] ]
      [ widgetControlsCount , widgetControlsFilters , widgetControlsClear ]

widgetControlsCount :: EntriesWidget a
widgetControlsCount = do
  elist <- get
  elT E.span
      [ A.class_ "todo-count" ]
      [ elT E.strong [] [ lift $ text (fromString $ show $ entriesLeft elist) ]
      , lift $ text $ (if entriesLeft elist == 1 then " item" else " items") ++ " left"
      ]

widgetControlsFilters :: EntriesWidget ()
widgetControlsFilters = elT_ E.ul [ A.class_ "filters" ] $ do
  elist <- get
  newVisibility <- lift $ visibilityWidget $ entriesVisibility elist
  put $ elist { entriesVisibility = newVisibility }
  where
    visibilityWidget :: EntriesVisibility -> Widget HTML EntriesVisibility
    visibilityWidget visibility = orr $ intersperse (text " ") $
      [ visibilitySwap "#/" "All" All visibility
      , visibilitySwap "#/active" "Active" Active visibility
      , visibilitySwap "#/completed" "Completed" Completed visibility
      ]
    visibilitySwap :: String -> String -> EntriesVisibility -> EntriesVisibility -> Widget HTML EntriesVisibility
    visibilitySwap uri label visibility actualVisibility = do
      clickEl E.li [] (const visibility)
        [ el_ E.a
            [ A.href $ fromString uri, classList [("selected", visibility == actualVisibility)] ] $
              text label
        ]

widgetControlsClear :: EntriesWidget ()
widgetControlsClear = do
  elist <- get
  _ <- lift $ clickEl E.button
      [ classList [("clear-completed", True), ("hidden", entriesCompleted elist == 0)] ]
      (const ())
      [ text ("Clear completed (" ++ fromString (show $ entriesCompleted elist) ++ ")") ]
  put $ elist { entriesList = filter (not . entryCompleted) (entriesList elist) }
