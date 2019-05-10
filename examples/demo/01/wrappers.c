/*
 * Copyright (c) 2019-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
#include <stdlib.h>

int* allocate_int() { return malloc(sizeof(int)); }

void set(int* p, int value) { *p = value; }
