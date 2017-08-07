{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad        (forever, void)
import           Control.Monad.State  (StateT, execStateT, get, lift, put)

import qualified Data.JSString        as JSS
import           Data.List            (intersperse)
import           Data.String          (fromString)
import           Data.Void

import qualified GHCJS.VDOM.Attribute as A
import qualified GHCJS.VDOM.Element   as E
import qualified GHCJS.VDOM.Event     as Ev

import           Concur               (HTML, Widget, classList, clickEl, el,
                                       elEvent, el_, initConcur,
                                       inputEnter, never, orr, runWidgetInBody,
                                       text)

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
widgetTodos = forever $ el E.div [ A.class_ "todomvc-wrapper" ]
  [ el E.section [A.class_ "todoapp"] [widgetInput, widgetEntries, widgetControls]
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

widgetInput :: EntriesWidget ()
widgetInput = el E.header
  [ A.class_ "header" ]
  [ el E.h1 [] [lift $ text "todos"]
  , do
      elist <- get
      s <- lift $ inputEnter [A.class_ "new-todo", A.placeholder "What needs to be done?", A.autofocus "autofocus", A.name "newTodo", A.value ""]
      put $ elist { entriesList = Entry s False : entriesList elist }
  ]

widgetEntries :: EntriesWidget ()
widgetEntries = do
  elist <- get
  el E.section [ classList [("main", True), ("hidden", null $ entriesList elist)] ]
    [ lift (allCompletedToggle (allCompleted elist)) >>= put . flip markAllComplete elist
    , el_ E.ul [ A.class_ "todo-list" ] $ elistToEntriesListWidget elist
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


widgetEntry :: Entry -> Widget HTML (Maybe Entry)
widgetEntry todo = go False
  where
    go editing = ego editing >>= either go return
    ego editing = do
      el E.li [ classList [ ("completed", completed), ("editing", editing) ] ] $
        [ el E.div [ A.class_ "view" ] $
            [ clickEl E.input (addChecked completed [A.type_ "checkbox", A.class_ "toggle"])
                (\_e -> Right $ Just $ todo { entryCompleted = not completed }) []
            , either (const $ Left $ not editing) absurd <$> elEvent Ev.dblclick E.label [] (text desc)
            , clickEl E.button [A.class_ "destroy"] (const $ Right Nothing) []
            ]
        , if editing
            then fmap (\desc' -> Right $ Just $ todo { entryDescription = desc' }) $
                   inputEnter [A.autofocus "autofocus", A.class_ "edit", A.name "title", A.value $ JSS.pack desc]
            else never
        ]
    completed = entryCompleted todo
    desc = entryDescription todo
    addChecked v l = if v then (A.checked "checked" : l) else l

widgetControls :: EntriesWidget ()
widgetControls = do
  elist <- get
  el E.footer
      [ classList [("footer", True), ("hidden", null $ entriesList elist)] ]
      [ widgetControlsCount , widgetControlsFilters , widgetControlsClear ]

widgetControlsCount :: EntriesWidget a
widgetControlsCount = do
  elist <- get
  el E.span
      [ A.class_ "todo-count" ]
      [ el E.strong [] [ lift $ text (fromString $ show $ entriesLeft elist) ]
      , lift $ text $ (if entriesLeft elist == 1 then " item" else " items") ++ " left"
      ]

widgetControlsFilters :: EntriesWidget ()
widgetControlsFilters = el_ E.ul [ A.class_ "filters" ] $ do
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
