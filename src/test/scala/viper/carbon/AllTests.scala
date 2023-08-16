// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon

import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier
import viper.silver.frontend.Frontend
import java.nio.file.Path

import viper.silver.logger.SilentLogger
import viper.silver.reporter.{NoopReporter, StdIOReporter}

/** All tests for carbon.

  */
class AllTests extends SilSuite {
  override def testDirectories: Seq[String] = Vector(
    "examples"
    //"local", "all", "quantifiedpermissions", "quantifiedpredicates", "quantifiedcombinations",
    //"wands", "examples", "termination", "refute", "quasihavoc"
  )

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  val carbon: CarbonVerifier = CarbonVerifier(StdIOReporter())

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    carbon.parseCommandLine(Seq("--counterexample", "extended") :+ "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver.vpr")
  }
  //Seq("--counterexample", "intermediate") :+

  lazy val verifiers = List(CarbonVerifier(StdIOReporter()))
}
