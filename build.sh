FOLDER=./src
MIN_DEPTH=1
MAX_DEPTH=1

REVEALJS_THEME=blood

find $FOLDER -iname "*.md" -mindepth $MIN_DEPTH -maxdepth $MAX_DEPTH -type f -exec sh -c 'pandoc -t revealjs --slide-level=2 -s -o "./docs/$(basename ${0%.md}.html)" "${0}" --include-in-header=./css/common.css --include-in-header=./js/highlight.js -V theme=$REVEALJS_THEME' {} \;
