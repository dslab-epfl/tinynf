# tested on Ubuntu 18.04 and 20.04
# THIS SCRIPT SHOULD BE SOURCED NOT RAN

VIRTENV_NAME='tinynf-experiments'

if [ ! -d "$HOME/.virtualenvs/$VIRTENV_NAME" ]; then
  sudo apt install -y python3.8 python3-pip
  python3.8 -m pip install virtualenv virtualenvwrapper
  mkdir -p "$HOME/.virtualenvs"
fi

export WORKON_HOME="$HOME/.virtualenvs"
export VIRTUALENVWRAPPER_PYTHON="$(which python3.8)"
export VIRTUALENVWRAPPER_VIRTUALENV="$HOME/.local/bin/virtualenv"
. "$HOME/.local/bin/virtualenvwrapper.sh"

if [ -d "$HOME/.virtualenvs/$VIRTENV_NAME" ]; then
  workon "$VIRTENV_NAME"
else
  mkvirtualenv "$VIRTENV_NAME"
  pip install -r requirements.txt
fi
