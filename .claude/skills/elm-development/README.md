# Elm Development Skill

A comprehensive guide to building reliable, maintainable web applications using Elm - a delightful functional programming language that compiles to JavaScript.

## Overview

Elm is a functional programming language that brings the best ideas from functional programming to front-end web development. With Elm, you can build web applications that have:

- **No runtime errors** in practice
- **Friendly error messages** that help you fix problems quickly
- **Reliable refactoring** with confidence
- **Automatically enforced semantic versioning**
- **Small, fast compiled output**
- **Great performance** by default

### Why Choose Elm?

**Reliability**: Elm's type system and compiler guarantee you won't see null/undefined errors, and you can refactor with confidence knowing the compiler will catch any issues.

**Developer Experience**: Elm provides the best error messages in the industry. When something goes wrong, the compiler doesn't just tell you what's wrong - it suggests how to fix it.

**Simplicity**: Elm's syntax is clean and minimal. There's usually one obvious way to do things, making it easy to read and understand Elm code.

**Performance**: Elm generates fast, optimized JavaScript. The virtual DOM implementation is one of the fastest available.

**Maintainability**: Elm code ages well. The strong type system and pure functions make it easy to understand and modify code even years later.

### When to Use Elm

Elm is excellent for:

- **Single Page Applications (SPAs)** - Elm's architecture makes complex state management simple
- **Interactive UIs** - Forms, dashboards, data visualizations
- **Long-lived applications** - The type system keeps large codebases manageable
- **Teams new to functional programming** - Elm is one of the most approachable FP languages
- **Projects requiring high reliability** - Financial applications, healthcare, critical business tools
- **Gradual migration** - You can embed Elm components in existing JavaScript applications

Elm may not be ideal for:

- **Simple static sites** - Use a static site generator instead
- **Heavy DOM manipulation** - Use JavaScript directly
- **Projects requiring specific JavaScript libraries** - Interop is possible but adds complexity
- **Rapid prototyping with frequent design changes** - Unless your team is already experienced with Elm

### Elm vs Other Options

**Elm vs React:**
- Elm: Stronger guarantees, no runtime errors, steeper learning curve
- React: Larger ecosystem, more flexibility, runtime errors possible

**Elm vs TypeScript:**
- Elm: Complete type safety, pure functional, limited JS interop
- TypeScript: JavaScript superset, gradual typing, full JS ecosystem access

**Elm vs Vue:**
- Elm: Functional architecture, immutability, compile-time guarantees
- Vue: Template-based, familiar to HTML developers, easier learning curve

**Elm vs Angular:**
- Elm: Simpler, functional, lighter weight
- Angular: Full framework, dependency injection, enterprise features

## Installation and Setup

### Installing Elm

**macOS:**
```bash
# Using Homebrew
brew install elm

# Using npm
npm install -g elm
```

**Linux:**
```bash
# Using npm
npm install -g elm

# Download binary from elm-lang.org
curl -L -o elm.gz https://github.com/elm/compiler/releases/download/0.19.1/binary-for-linux-64-bit.gz
gunzip elm.gz
chmod +x elm
sudo mv elm /usr/local/bin/
```

**Windows:**
```bash
# Using npm
npm install -g elm

# Or download installer from elm-lang.org
```

### Verify Installation

```bash
elm --version
# Should output: 0.19.1
```

### Editor Setup

**VS Code:**
```bash
# Install Elm extension
code --install-extension Elmtooling.elm-ls-vscode

# Install elm-format
npm install -g elm-format
```

**Vim/Neovim:**
```bash
# Install elm-vim plugin
# Add to your .vimrc or init.vim:
Plug 'elmcast/elm-vim'

# Install elm-format
npm install -g elm-format
```

**Sublime Text:**
```bash
# Install Elm Syntax Highlighting via Package Control
# Install LSP and LSP-elm packages
```

**IntelliJ/WebStorm:**
```bash
# Install Elm plugin from JetBrains marketplace
# Settings → Plugins → Search "Elm" → Install
```

### Essential Tools

**elm-format** - Code formatter:
```bash
npm install -g elm-format

# Format a file
elm-format src/Main.elm --yes

# Format entire directory
elm-format src/ --yes
```

**elm-test** - Testing framework:
```bash
npm install -g elm-test

# Initialize tests
elm-test init

# Run tests
elm-test
```

**elm-review** - Linter and code analyzer:
```bash
npm install -g elm-review

# Initialize
elm-review init

# Run review
elm-review
```

**elm-live** - Development server with live reload:
```bash
npm install -g elm-live

# Start dev server
elm-live src/Main.elm -- --output=main.js
```

## Quick Start

### Creating Your First Elm Application

**1. Initialize a new project:**
```bash
mkdir my-elm-app
cd my-elm-app
elm init
```

This creates:
- `elm.json` - Package configuration
- `src/` - Source code directory

**2. Create your first Elm file:**

Create `src/Main.elm`:
```elm
module Main exposing (main)

import Browser
import Html exposing (Html, button, div, text)
import Html.Events exposing (onClick)

-- MODEL

type alias Model = Int

init : Model
init = 0

-- UPDATE

type Msg = Increment | Decrement

update : Msg -> Model -> Model
update msg model =
    case msg of
        Increment ->
            model + 1

        Decrement ->
            model - 1

-- VIEW

view : Model -> Html Msg
view model =
    div []
        [ button [ onClick Decrement ] [ text "-" ]
        , div [] [ text (String.fromInt model) ]
        , button [ onClick Increment ] [ text "+" ]
        ]

-- MAIN

main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }
```

**3. Compile and run:**
```bash
# Compile to JavaScript
elm make src/Main.elm --output=main.js

# Or use elm reactor for development
elm reactor
# Open http://localhost:8000
# Navigate to src/Main.elm
```

**4. Create an HTML file:**

Create `index.html`:
```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>My Elm App</title>
    <script src="main.js"></script>
</head>
<body>
    <div id="app"></div>
    <script>
        var app = Elm.Main.init({
            node: document.getElementById('app')
        });
    </script>
</body>
</html>
```

**5. Open in browser:**
```bash
# Open index.html in your browser
open index.html
```

### Development Workflow

**Using elm-live for hot reload:**
```bash
# Install elm-live
npm install -g elm-live

# Start development server
elm-live src/Main.elm --open -- --output=main.js --debug

# The --debug flag enables time-travel debugging
```

**Building for production:**
```bash
# Compile with optimization
elm make src/Main.elm --output=main.js --optimize

# Minify (requires uglify-js)
uglifyjs main.js --compress 'pure_funcs=[F2,F3,F4,F5,F6,F7,F8,F9,A2,A3,A4,A5,A6,A7,A8,A9],pure_getters,keep_fargs=false,unsafe_comps,unsafe' | uglifyjs --mangle --output=main.min.js
```

## Project Structure

### Recommended Directory Layout

```
my-elm-app/
├── elm.json                    # Package configuration
├── src/
│   ├── Main.elm               # Application entry point
│   ├── Models/                # Data models
│   │   ├── User.elm
│   │   ├── Post.elm
│   │   └── Comment.elm
│   ├── Views/                 # View components
│   │   ├── Home.elm
│   │   ├── Profile.elm
│   │   ├── Common/
│   │   │   ├── Header.elm
│   │   │   ├── Footer.elm
│   │   │   └── Button.elm
│   │   └── Layout.elm
│   ├── Pages/                 # Page-level components
│   │   ├── Home.elm
│   │   ├── Profile.elm
│   │   └── Settings.elm
│   ├── Api/                   # API communication
│   │   ├── User.elm
│   │   ├── Post.elm
│   │   └── Endpoints.elm
│   ├── Utils/                 # Utility functions
│   │   ├── Validators.elm
│   │   ├── Formatters.elm
│   │   └── Helpers.elm
│   └── Ports.elm              # JavaScript interop
├── tests/                     # Test files
│   ├── UserTests.elm
│   ├── ValidatorTests.elm
│   └── Tests.elm
├── public/                    # Static assets
│   ├── index.html
│   ├── styles.css
│   ├── favicon.ico
│   └── assets/
│       ├── images/
│       └── fonts/
├── dist/                      # Build output (gitignored)
├── .gitignore
├── README.md
└── package.json               # npm dependencies (for tooling)
```

### Module Organization Patterns

**By Feature:**
```
src/
├── Main.elm
├── Auth/
│   ├── Login.elm
│   ├── Register.elm
│   └── Models.elm
├── Dashboard/
│   ├── Overview.elm
│   ├── Charts.elm
│   └── Models.elm
└── Settings/
    ├── Profile.elm
    ├── Preferences.elm
    └── Models.elm
```

**By Layer:**
```
src/
├── Main.elm
├── Models/
│   ├── User.elm
│   ├── Post.elm
│   └── Settings.elm
├── Views/
│   ├── UserView.elm
│   ├── PostView.elm
│   └── SettingsView.elm
└── Updates/
    ├── UserUpdate.elm
    ├── PostUpdate.elm
    └── SettingsUpdate.elm
```

## Understanding elm.json

### Application Configuration

```json
{
    "type": "application",
    "source-directories": [
        "src"
    ],
    "elm-version": "0.19.1",
    "dependencies": {
        "direct": {
            "elm/browser": "1.0.2",
            "elm/core": "1.0.5",
            "elm/html": "1.0.0",
            "elm/http": "2.0.0",
            "elm/json": "1.1.3",
            "elm/time": "1.0.0",
            "elm/url": "1.0.0"
        },
        "indirect": {
            "elm/bytes": "1.0.8",
            "elm/file": "1.0.5",
            "elm/virtual-dom": "1.0.3"
        }
    },
    "test-dependencies": {
        "direct": {
            "elm-explorations/test": "2.1.2"
        },
        "indirect": {
            "elm/random": "1.0.0"
        }
    }
}
```

**Key Fields:**
- `type`: "application" or "package"
- `source-directories`: Where to find Elm source files
- `elm-version`: Elm compiler version
- `dependencies.direct`: Packages you use directly
- `dependencies.indirect`: Packages required by your dependencies
- `test-dependencies`: Packages for testing only

### Installing Packages

```bash
# Install a package
elm install elm/http
elm install elm/json
elm install elm/random

# Packages are automatically added to elm.json
```

### Popular Packages

**Core Packages:**
- `elm/browser` - Browser programs and navigation
- `elm/html` - HTML generation
- `elm/core` - Core language functionality
- `elm/json` - JSON encoding and decoding
- `elm/http` - HTTP requests
- `elm/time` - Working with time
- `elm/url` - URL parsing and building
- `elm/random` - Random value generation

**Community Packages:**
- `elm-community/list-extra` - Extended list functions
- `elm-community/maybe-extra` - Extended Maybe functions
- `elm-community/result-extra` - Extended Result functions
- `NoRedInk/elm-json-decode-pipeline` - Easier JSON decoding
- `rtfeldman/elm-css` - Type-safe CSS
- `elm-explorations/markdown` - Markdown rendering

## Common Development Tasks

### Adding a New Page

1. Create the page module:
```elm
module Pages.About exposing (view)

import Html exposing (..)
import Html.Attributes exposing (..)

view : Html msg
view =
    div [ class "about-page" ]
        [ h1 [] [ text "About Us" ]
        , p [] [ text "Welcome to our application!" ]
        ]
```

2. Add route to router:
```elm
type Route
    = Home
    | About
    | NotFound

routeParser : Parser (Route -> a) a
routeParser =
    oneOf
        [ Parser.map Home top
        , Parser.map About (s "about")
        ]
```

3. Update view function:
```elm
viewRoute : Route -> Html Msg
viewRoute route =
    case route of
        Home ->
            Pages.Home.view

        About ->
            Pages.About.view

        NotFound ->
            Pages.NotFound.view
```

### Making API Calls

1. Define your data model:
```elm
type alias User =
    { id : Int
    , name : String
    , email : String
    }
```

2. Create a decoder:
```elm
import Json.Decode as Decode

userDecoder : Decode.Decoder User
userDecoder =
    Decode.map3 User
        (Decode.field "id" Decode.int)
        (Decode.field "name" Decode.string)
        (Decode.field "email" Decode.string)
```

3. Make the request:
```elm
import Http

type Msg
    = GotUser (Result Http.Error User)

fetchUser : Int -> Cmd Msg
fetchUser userId =
    Http.get
        { url = "/api/users/" ++ String.fromInt userId
        , expect = Http.expectJson GotUser userDecoder
        }
```

4. Handle the response:
```elm
update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
    case msg of
        GotUser result ->
            case result of
                Ok user ->
                    ( { model | user = Just user }
                    , Cmd.none
                    )

                Err _ ->
                    ( { model | error = Just "Failed to load user" }
                    , Cmd.none
                    )
```

### Working with Forms

1. Define form model:
```elm
type alias LoginForm =
    { email : String
    , password : String
    , errors : List String
    }
```

2. Create form messages:
```elm
type Msg
    = UpdateEmail String
    | UpdatePassword String
    | SubmitForm
```

3. Build the view:
```elm
viewLoginForm : LoginForm -> Html Msg
viewLoginForm form =
    Html.form [ onSubmit SubmitForm ]
        [ input
            [ type_ "email"
            , value form.email
            , onInput UpdateEmail
            , placeholder "Email"
            ]
            []
        , input
            [ type_ "password"
            , value form.password
            , onInput UpdatePassword
            , placeholder "Password"
            ]
            []
        , button [ type_ "submit" ] [ text "Login" ]
        , viewErrors form.errors
        ]
```

### Debugging

**Time-Travel Debugger:**
```bash
# Compile with debug mode
elm make src/Main.elm --output=main.js --debug
```

This enables the Elm debugger which shows:
- All messages and state changes
- Ability to pause, rewind, and replay
- Import/export of state history

**Console Logging via Ports:**
```elm
port module Main exposing (..)

port log : String -> Cmd msg

update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
    case msg of
        SomeMsg ->
            ( newModel
            , log ("Debug: " ++ Debug.toString newModel)
            )
```

## Testing

### Writing Tests

Create `tests/Tests.elm`:
```elm
module Tests exposing (..)

import Test exposing (..)
import Expect
import Validators exposing (validateEmail)

suite : Test
suite =
    describe "Validators"
        [ describe "validateEmail"
            [ test "accepts valid email" <|
                \_ ->
                    validateEmail "test@example.com"
                        |> Expect.equal (Ok "test@example.com")

            , test "rejects invalid email" <|
                \_ ->
                    validateEmail "not-an-email"
                        |> Expect.err
            ]
        ]
```

### Running Tests

```bash
# Run all tests
elm-test

# Run in watch mode
elm-test --watch

# Run specific file
elm-test tests/ValidatorTests.elm
```

## Deployment

### Building for Production

```bash
# 1. Compile with optimization
elm make src/Main.elm --output=dist/elm.js --optimize

# 2. Minify JavaScript
uglifyjs dist/elm.js --compress 'pure_funcs=[F2,F3,F4,F5,F6,F7,F8,F9,A2,A3,A4,A5,A6,A7,A8,A9],pure_getters,keep_fargs=false,unsafe_comps,unsafe' | uglifyjs --mangle --output=dist/elm.min.js

# 3. Gzip for serving
gzip -c dist/elm.min.js > dist/elm.min.js.gz
```

### Static Hosting

Elm apps are just static files - deploy to:
- **Netlify**: Drag and drop or connect to Git
- **Vercel**: `vercel` command or Git integration
- **GitHub Pages**: Push to gh-pages branch
- **AWS S3**: Upload to S3 bucket with static hosting
- **Firebase Hosting**: `firebase deploy`

### Example netlify.toml

```toml
[build]
  command = "elm make src/Main.elm --output=main.js --optimize"
  publish = "."

[[redirects]]
  from = "/*"
  to = "/index.html"
  status = 200
```

## Learning Path

### Beginner Path

1. **Read the Official Guide**: https://guide.elm-lang.org (takes 2-3 hours)
2. **Build a Counter App**: Understand Model-Update-View
3. **Add User Input**: Forms and validation
4. **Make HTTP Requests**: Fetch data from an API
5. **Handle Loading States**: RemoteData pattern

### Intermediate Path

1. **Learn Routing**: Build a multi-page SPA
2. **Master JSON Decoding**: Complex nested structures
3. **Use Ports**: Interact with JavaScript
4. **Write Tests**: Unit tests for your functions
5. **Optimize Performance**: Html.Lazy and profiling

### Advanced Path

1. **Custom Types Mastery**: Make impossible states impossible
2. **Advanced Patterns**: Debouncing, caching, optimistic updates
3. **Large App Architecture**: Module organization and scaling
4. **Port Modules**: Complex JavaScript interop
5. **Contribution**: Contribute to Elm packages

## Troubleshooting

### Common Issues

**"I can't find package X"**
- Search on https://package.elm-lang.org
- Many JavaScript libraries don't have Elm equivalents
- Use ports to integrate JavaScript libraries

**"The compiler error is confusing"**
- Read the entire error message carefully
- The compiler usually suggests fixes
- Check the Elm Slack or Discourse for help

**"My app is slow"**
- Use Html.Lazy for expensive views
- Profile with the Elm debugger
- Check for unnecessary re-renders

**"How do I do X in Elm?"**
- Check the official guide first
- Search Elm Discourse
- Ask on Elm Slack
- The answer is usually "with pure functions"

## Resources

### Official Resources
- **Elm Guide**: https://guide.elm-lang.org
- **Package Docs**: https://package.elm-lang.org
- **Elm Discourse**: https://discourse.elm-lang.org
- **Elm Slack**: https://elmlang.herokuapp.com
- **Elm Radio Podcast**: https://elm-radio.com

### Books
- **Elm in Action** by Richard Feldman
- **Programming Elm** by Jeremy Fairbank
- **Practical Elm** by Alex Korban

### Video Courses
- **Elm for Beginners** (Udemy)
- **Advanced Elm** (Frontend Masters)
- **Elm Conf Talks** (YouTube)

### Community
- **Elm Weekly** - Newsletter
- **Elm Discourse** - Forum
- **r/elm** - Reddit community
- **Twitter**: Follow @elmlang

## Next Steps

After reading this guide:

1. **Read SKILL.md** - Deep dive into all Elm concepts
2. **Study EXAMPLES.md** - 15+ practical code examples
3. **Build something real** - Start a small project
4. **Join the community** - Elm Slack and Discourse
5. **Read Elm in Action** - Comprehensive book

Happy Elm coding!
