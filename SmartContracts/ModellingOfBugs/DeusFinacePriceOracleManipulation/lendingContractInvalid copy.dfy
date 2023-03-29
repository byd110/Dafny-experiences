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

  var collateral : nat;
  var token1 : nat;
  var token2 : nat;
  // var lastinquire : nat;
  // var timestamp : nat;
  // var lastprice : nat;
  ghost var inv : nat;
  const MAX_UINT256 : nat := (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 as nat - 1)


  predicate valid()
    reads this
  {
    token1 * token2 == inv && token2 != 0 && token1 != 0

  }

  // applicaiotn contract function using price oracle data
  function method customized_price () : nat
    requires valid()
    // requires timestamp >= lastinquire
    reads this

  {
    token1 / token2
  }

  // update data from price oracle
  method update (tok1 : nat, tok2 : nat)
    requires valid()
    requires tok1 * tok2 == inv
    requires tok2 != 0

    modifies this

    ensures valid()
    ensures inv == old(inv)
    ensures token1 == tok1 && token2 == tok2
    // ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)
    // ensures lastprice == old(lastprice)
    ensures collateral == old(collateral)
  {
    // lastprice := token1 / token2;
    token1 := tok1;
    token2 := tok2;
  }

  method mutate ()
    requires valid()
    requires inv >= 4
    // requires token1 < MAX_UINT256 && token2 < MAX_UINT256
    // ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)

    modifies this

    ensures valid()
    ensures inv == old(inv)
    ensures token1 != old(token1) && token2 != old(token2)
    // ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)
    // ensures lastprice == old(lastprice)
    ensures collateral == old(collateral)
  {
    var m : nat := mut();
    var data1m := token1 * m;
    var data2m := token2 / m;
    update(data1m, data2m);
    // assume(token1 != old(token1) && token2 != old(token2));
  }

  method transactions(amount : nat) returns ( price : nat)
    requires valid()
    requires amount > 0
    requires collateral != 0
    requires amount  > token1 / token2 * collateral
    requires inv >= 4
    // requires lastinquire == timestamp

    modifies this

    ensures  price * collateral < amount

  {
    // lastprice := token1 / token2;
    // assert(lastprice * collateral < amount);
    mutate();
    // test();
    price := customized_price();
    // assert(price == lastprice);
    // assert(lastprice * collateral < amount);
  }

  method  mut() returns (a: nat)
    ensures a > 0 && a != 1
    ensures inv % a == 0 && token2 % a == 0

  method test()
    ensures token1 != old(token1) && token2 != old(token2)
    ensures token1 * token2 == old(token1) * old(token2) == inv
}

method {:extern} havoc() returns (a: nat)
  ensures a != 0



