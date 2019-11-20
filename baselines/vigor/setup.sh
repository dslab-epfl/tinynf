git submodule update --init --recursive

# Simplified version of the vigor setup script, with only what we need to run Vigor on top of our code

sudo apt-get install -y opam m4 python3.6
opam init -y
opam switch 4.06.0
opam install goblint-cil core ocamlfind -y

if ! grep -q opam "$HOME/.profile"; then
  echo 'PATH='"$HOME/.opam/system/bin"':$PATH' >> "$HOME/.profile"
  echo ". $HOME/.opam/opam-init/init.sh" >> "$HOME/.profile"
  . "$HOME/.profile"
fi
