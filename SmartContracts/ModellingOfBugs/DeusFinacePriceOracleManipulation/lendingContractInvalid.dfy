/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "./NonNativeTypes.dfy"
include "./Contract.dfy"
  // include "./Token.dfy"

import opened NonNativeTypes

datatype Msg = Msg(sender: Account, value: uint256)
datatype Try<T> = Success(v: T) | Revert()

type Address = Account

class LendingContract  {

  var collateral : real;
  var token1 : real;
  var token2 : real;
  ghost var inv : real;
  predicate valid()
    reads this
  {
    token1 * token2 == inv && token2 != 0.0 && token1 != 0.0
  }

  // applicaiotn contract function using price oracle data
  function method customized_price () : real
    requires valid()
    reads this
  {
    token1 / token2
  }

  // update data from price oracle
  method update (tok1 : real, tok2 : real)
    requires valid()
    requires tok1 * tok2 == inv
    requires tok2 != 0.0

    modifies this

    ensures valid()
    ensures inv == old(inv)
  {
    token1, token2 := tok1, tok2;
  }

  method inquire()
    requires valid()
    modifies this
    ensures valid()
  {
    var product := token1 * token2;
    var tok2 := havoc();
    var tok1 := product / tok2;
    update(tok1, tok2);
  }

  method mutate ()
    requires valid()

    modifies this

    ensures valid()
    ensures inv == old(inv)
  {
    var m : real := mut();
    var data1m := token1 * m;
    var data2m := token2 / m;
    update(data1m, data2m);
  }

  method transactions(amount : real) returns (r1: Try<()>, price : real)
    requires valid()
    requires amount > 0.0
    requires inv > 1.0

    modifies this

    ensures  r1.Revert? ==>  price * collateral < amount

  {
    collateral := havoc();
    inquire();
    price := customized_price();
    if (price * collateral < amount)
    {
      r1 := Revert();
      mutate();
      price := customized_price();
    }
    else
    {
      r1 := Success(());
    }
  }
}

method {:extern} havoc() returns (a: real)
  ensures a != 0.0

method {:extern} mut() returns (a: real)
  ensures 0.0 < a < 10.0 && a != 1.0

