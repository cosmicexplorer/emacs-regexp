/* Description: ???

Copyright (C) 2024 Danny McClanahan <dmcC2@hypnicjerk.ai>
SPDX-License-Identifier: GPL-3.0-or-later

This file is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 3 of the
License, or (at your option) any later version.

This file is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. */

use std::{env, fs, path::PathBuf};

fn main() {
  let crate_dir: PathBuf = env::var("CARGO_MANIFEST_DIR")
    .expect("CARGO_MANIFEST_DIR not set")
    .into();
  assert!(crate_dir.is_dir());

  let bindings = cbindgen::generate(crate_dir).expect("binding generation failed");
  let _ = fs::remove_file("src/rex.h");
  assert!(bindings.write_to_file("src/rex.h"));
}
