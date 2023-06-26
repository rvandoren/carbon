package viper.carbon.boogie

import scala.collection.{Seq, mutable}
import scala.collection.immutable._
import util.control.Breaks._
import viper.carbon.verifier.FailureContextImpl
import viper.silver.ast
import viper.silver.ast.{Literal, Member, Field, Predicate, Label}
import viper.silver.verifier.{AbstractError, ApplicationEntry, ConstantEntry, ValueEntry, FailureContext, MapEntry, Model, ModelEntry, SimpleCounterexample, UnspecifiedEntry, VerificationError}
import viper.silver.ast.{AbstractLocalVar, Declaration, LocalVar, MagicWandStructure, Program, Type}

case class CounterexampleGenerator(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]) {
  val ve = e.asInstanceOf[VerificationError]
  val errorMethod = ErrorMemberMapping.mapping.get(ve.methodIdentifier).get
  val imCE = IntermediateCounterexampleModel(ve, errorMethod, names, program, wandNames)
  println(imCE.toString)

  val ceStore = CounterexampleGenerator.detStore(program.methodsByName.get(errorMethod.name).get.transitiveScopedDecls, imCE.basicVariables, imCE.allCollections)
  var ceHeaps = Seq[(String, HeapCounterexample)]()
  imCE.allBasicHeaps.foreach { case (n, h) => ceHeaps +:= ((n, CounterexampleGenerator.detHeap(imCE.workingModel, h, program, imCE.allCollections))) }

  val DomainsAndFunctions = imCE.DomainEntries ++ imCE.nonDomainFunctions

  override def toString: String = {
    var finalString = "      Final Counterexample: \n"
    finalString += "   Store: \n"
    finalString += ceStore.storeEntries.map(x => x.toString).mkString("", "\n", "\n")
    finalString += ceHeaps.map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("")
    finalString += "   Domains: \n"
    finalString += DomainsAndFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }
}

case class IntermediateCounterexampleModel(ve: VerificationError, errorMethod: Member, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]) {
  val originalEntries = ve.failureContexts(0).counterExample.get.model
  println(originalEntries.entries.toString())
  val typenamesInMethod = names.get(errorMethod.name).get.map(e => e._2 -> e._1)
  val methodVarDecl = program.methodsByName.get(errorMethod.name).get.transitiveScopedDecls

  val (basicVariables, otherDeclarations) = IntermediateCounterexampleModel.detCEvariables(originalEntries.entries, typenamesInMethod, methodVarDecl)
  val allSequences = IntermediateCounterexampleModel.detSequences(originalEntries)
  val allSets = IntermediateCounterexampleModel.detSets(originalEntries)
  val allMultisets = IntermediateCounterexampleModel.detMultisets(originalEntries)
  val allCollections = allSequences ++ allSets ++ allMultisets

  val workingModel = IntermediateCounterexampleModel.buildNewModel(originalEntries.entries)
  val (hmLabels, hmStates) = IntermediateCounterexampleModel.oldAndReturnHeapMask(workingModel, otherDeclarations)
  val allBasicHeaps = IntermediateCounterexampleModel.detHeaps(workingModel, hmStates, originalEntries, hmLabels, program)

  val DomainEntries = IntermediateCounterexampleModel.getAllDomains(originalEntries, program)
  val nonDomainFunctions = IntermediateCounterexampleModel.getAllFunctions(originalEntries, program)

  override def toString: String = {
    var finalString = "      Intermediate Counterexample: \n"
    finalString ++= "   Local Information:\n"
    if (!basicVariables.isEmpty) finalString += basicVariables.map(x => x.toString).mkString("", "\n", "\n")
    if (!allCollections.isEmpty) finalString += allCollections.map(x => x.toString).mkString("", "\n", "\n")
    finalString += allBasicHeaps.map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("", "\n", "\n")
    finalString ++= "   Domains:\n"
    finalString += DomainEntries.map(x => x.toString).mkString("", "\n", "\n")
    finalString += nonDomainFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }
}

case class StoreCounterexample(storeEntries: Seq[StoreEntry]) {
  var finalString = ""
  storeEntries.foreach { se => finalString ++= se.toString + "\n"}
  override lazy val toString = finalString
}

case class StoreEntry(id: AbstractLocalVar, entry: CEValue) {
  override lazy val toString = {
    entry match {
      case CEVariable(_, _, _) => s"Variable Name: ${id.name}, Value: ${entry.value.toString}, Type: ${id.typ.toString}"
      case _ => s"Collection variable ${id.name} of type ${id.typ.toString}:\n${entry.toString}"
    }
  }
}

case class HeapCounterexample(heapEntries: Seq[(Member, FinalHeapEntry)]) {
  var finalString = ""
  heapEntries.foreach { se => finalString ++= se._2.toString ++ "\n" }
  override lazy val toString = finalString
}

sealed trait FinalHeapEntry
case class FieldFinalEntry(ref: String, field: String, entry: CEValue, perm: Option[Rational], typ: Type) extends FinalHeapEntry {
  override lazy val toString = s"Field Entry: $ref.$field --> (Value: ${entry.value.toString}, Type: ${typ}, Perm: ${perm.getOrElse("#undefined").toString})"
}

case class PredFinalEntry(name: String, args: Seq[String], perm: Option[Rational]) extends FinalHeapEntry {
  override lazy val toString = s"Predicate Entry: $name(${args.mkString("", ", ", ")")} --> (Perm: ${perm.getOrElse("#undefined").toString})"
}

case class WandFinalEntry(firstPart: String, secondPart: String, args: Seq[String], perm: Option[Rational]) extends FinalHeapEntry {
  override lazy val toString = "to do"
}

case class DomainsCounterxample() {}

case class FunctionFinalEntry(name: String, argtypes: Seq[ast.Type], returnType: ast.Type, options: Map[Seq[CEValue], CEValue], default: CEValue) {

}

sealed trait CEValue {
  val id : String
  val value : Any
  val valueType : Option[ast.Type]
}

case class CEVariable(name: String, entryValue: ModelEntry, typ: Option[Type]) extends CEValue {
  val id = name
  val value = entryValue
  val valueType = typ
  override lazy val toString = s"Variable Name: ${name}, Value: ${value.toString}, Type: ${typ.getOrElse("Not determined!").toString}"
}

case class CESequence(name: String, length: BigInt, entries: Map[BigInt, String], sequence: Seq[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = sequence
  val valueType = memberTypes
  val size = length
  val inside = entries
  override lazy val toString = {
    var finalString = s"$name with size ${size.toString()} with entries:"
    for ((k,v) <- inside)
      finalString ++= s"\n $v at index ${k.toString()}"
    finalString
  }
}

case class CESet(name: String, cardinality: BigInt, containment: Map[String, Boolean], set: Set[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = set
  val valueType = memberTypes
  val size = cardinality
  val inside = containment
  override lazy val toString = {
    var finalString = s"Set $name of size ${size.toString()} with entries: {"
    for ((k, v) <- inside) {
      if (v) {
        finalString ++= s" $k,"
      }
    }
    finalString ++ "}"
  }
}

case class CEMultiset(name: String, cardinality: BigInt, containment: Map[String, Int], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = containment
  val valueType = memberTypes
  val size = cardinality
  override lazy val toString = {
    var finalString = s"Multiset $name of size ${size.toString()} with entries:"
    for ((k, v) <- containment)
      finalString ++= s"\n $k occurs ${v.toString} time"
    finalString
  }
}

case class BasicHeap(basicHeapEntries: Set[BasicHeapEntry]) {
  override lazy val toString = basicHeapEntries.map(x => x.toString).mkString("", "\n", "")
}

case class BasicHeapEntry(reference: Seq[String], field: Seq[String], valueID: String, perm: Option[Rational], het: HeapEntryType) {
  override lazy val toString = s"Basic heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Value: $valueID, Permission: ${perm.getOrElse("None")})"
}

case class BasicDomainEntry(name: String, types: Seq[ast.Type], functions: Seq[BasicFunction]) {
  override def toString: String = s"domain $valueName{\n ${functions.map(_.toString()).mkString("\n")}\n}"
  val valueName: String = s"$name${printTypes()}"
  private def printTypes(): String =
    if (types.isEmpty) ""
    else types.map(printType).mkString("[", ", ", "]")
  private def printType(t: ast.Type): String = t match {
    case ast.TypeVar(x) => x
    case _ => t.toString()
  }
}


case class BasicFunction(fname: String, argtypes: Seq[ast.Type], returnType: ast.Type, options: Map[Seq[String], String], default: String) {
  override def toString: String = {
    if (options.nonEmpty)
      s"$fname${argtypes.mkString("(", ",", ")")}:${returnType}{\n" + options.map(o => "    " + o._1.mkString(" ") + " -> " + o._2).mkString("\n") + "\n    else -> " + default + "\n}"
    else
      s"$fname{\n    " + default + "\n}"
  }
}

object IntermediateCounterexampleModel {

  def detCEvariables(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String], variables: Seq[Declaration]): (Seq[CEVariable], Seq[Declaration]) = {
    var res = Seq[CEVariable]()
    var otherDeclarations = Seq[Declaration]()
    val modelVariables = transformModelEntries(originalEntries, namesInMember)
    for ((name, entry) <- modelVariables) {
      for (temp <- variables) {
        if (temp.isInstanceOf[ast.LocalVarDecl]) {
          val v = temp.asInstanceOf[ast.LocalVarDecl]
          if (v.name == name) {
            var ent = entry
            if (entry.isInstanceOf[MapEntry]) {
              ent = entry.asInstanceOf[MapEntry].options.head._1(0)
            }
            res +:= CEVariable(v.name, ent, Some(v.typ))
          }
        } else {
          otherDeclarations +:= temp
        }
      }
    }
    if (originalEntries.contains("null")) {
      val nullRef = originalEntries.get("null").get
      if (nullRef.isInstanceOf[ConstantEntry]) {
        res +:= CEVariable("null", nullRef, Some(ast.Ref))
      }
    }
    (res, otherDeclarations)
  }

  def transformModelEntries(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]): mutable.Map[String, ModelEntry] = {
    val newEntries = mutable.HashMap[String, ModelEntry]()
    val currentEntryForName = mutable.HashMap[String, String]()
    for ((vname, e) <- originalEntries) {
      var originalName = vname
      if (originalName.startsWith("q@")) {
        originalName = originalName.substring(2)
      } else if (originalName.indexOf("@@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@@"))
      } else if (originalName.indexOf("@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@"))
      }
      if (PrettyPrinter.backMap.contains(originalName)) {
        val originalViperName = PrettyPrinter.backMap.get(originalName).get
        if (namesInMember.contains(originalViperName)) {
          val viperName = namesInMember.get(originalViperName).get
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)) {
            newEntries.update(viperName, e)
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    newEntries
  }

  def isLaterVersion(firstName: String, originalName: String, secondName: String): Boolean = {
    if ((secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1) && !"@@.*!".r.findFirstIn(firstName).isDefined) {
      true
    } else if (secondName.indexOf("@") != -1 && firstName.indexOf("@@") == -1 && firstName.indexOf("@") != -1) {
      val firstIndex = Integer.parseInt(firstName.substring(firstName.indexOf("@") + 1))
      val secondIndex = Integer.parseInt(secondName.substring(secondName.indexOf("@") + 1))
      firstIndex > secondIndex
    } else {
      false
    }
  }

  // a CE generator for sequences
  def detSequences(model: Model): Set[CEValue] = {
    var res = Map[String, Seq[String]]()
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq#Length") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (k(0).toString -> Seq.fill(v.toString.toInt)("#undefined"))
          }
        }
      } else if (opName == "Seq#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq())
          }
        }
      } else if (opName == "Seq#Append" || opName == "Seq#Take" || opName == "Seq#Drop" || opName == "Seq#Index") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq(k(0).toString))
          }
        }
      }
      if (opName == "Seq#Range") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq.range(k(0).toString.toInt, k(1).toString.toInt).map(x => x.toString))
          }
        }
      }
    }
    var found = true
    while (found) {
      found = false
      for (((opName, k), v) <- tempMap) {
        if (opName == "Seq#Append") {
          (res.get(k(0)), res.get(k(1))) match {
            case (Some(x), Some(y)) =>
              if (!res.contains(v)) {
                res += (v -> (x ++ y))
                tempMap -= ((opName, k))
                found = true
              }
            case (_, _) => //
          }
        } else if (opName == "Seq#Take") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.take(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case None => //
          }
        } else if (opName == "Seq#Drop") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.drop(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case None => //
          }
        } else if (opName == "Seq#Index") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (k(0) -> x.updated(k(1).toInt, v))
              tempMap -= ((opName, k))
              found = true
            case None => //
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SeqType(x))
          case None => None
        }
        var entries = Map[BigInt, String]()
        var counter = 0
        for (e <- s) {
          if (e != "#undefined") {
            entries += (BigInt(counter) -> e)
          }
          counter += 1
        }
        ans += CESequence(n, BigInt(s.length), entries, s, typ)
    }
    ans
  }

  // a CE generator for sets
  def detSets(model: Model): Set[CEValue] = {
    var res = Map[String, Set[String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Set())
        }
      }
      if (opName == "Set#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
          }
        }
      }
      if (opName == "Set#Card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Set())
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#UnionOne") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        res.get(k(0)) match {
          case Some(x) =>
            res += (v -> x.union(Set(k(1))))
            tempMap -= ((opName, k))
          case None => //
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#Union" || opName== "Set#Difference" || opName == "Set#Intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstSet = res.get(k(0))
        val secondSet = res.get(k(1))
        if ((firstSet != None) && (secondSet != None)) {
          if (opName == "Set#Union") {
            res += (v -> firstSet.get.union(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set#Intersection") {
            res += (v -> firstSet.get.intersect(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set#Difference") {
            res += (v -> firstSet.get.diff(secondSet.get))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        var containment = Map[String, Boolean]()
        for (e <- s) {
          if (e != "#undefined") {
            containment += (e -> true)
          }
        }
        ans += CESet(n, BigInt(s.size), containment, s, typ)
    }
    ans
  }

  // a CE generator for Multisets
  def detMultisets(model: Model): Set[CEValue] = {
    var res = Map[String, Map[String, Int]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map[String, Int]())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Map[String, Int]())
        }
      }
      if (opName == "MultiSet#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map(k(0).toString -> 1))
          }
        }
      }
      if (opName == "MultiSet#Select") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (!k(1).toString.startsWith("T@U!val!") && !v.toString.startsWith("0")) {
              res += (k(0).toString -> res.getOrElse(k(0).toString, Map.empty).updated(k(1).toString, v.toString.toInt))
            }
          }
        }
      }
      if (opName == "MultiSet#Card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Map[String, Int]())
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#UnionOne") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        res.get(k(0)) match {
          case Some(x) =>
            res += (v -> x.updated(k(1), x.getOrElse(k(1), 0)+1))
            tempMap -= ((opName, k))
          case None => //
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#Union" || opName == "MultiSet#Difference" || opName == "MultiSet#Intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstMultiset = res.get(k(0))
        val secondMultiset = res.get(k(1))
        if ((firstMultiset != None) && (secondMultiset != None)) {
          if (opName == "MultiSet#Union") {
            res += (v -> (firstMultiset.get.keySet ++ secondMultiset.get.keySet).map { key =>
              (key -> (firstMultiset.get.getOrElse(key, 0) + secondMultiset.get.getOrElse(key, 0)))
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "MultiSet#Intersection") {
            res += (v -> (firstMultiset.get.keySet & secondMultiset.get.keySet).map { key =>
              key -> Math.min(firstMultiset.get.get(key).get, secondMultiset.get.get(key).get)
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "MultiSet#Difference") {
            res += (v -> (firstMultiset.get.map { case (key, count) =>
              key -> (count - secondMultiset.get.getOrElse(key, 0))
            }.filter(_._2 > 0) ++ secondMultiset.get.filter { case (key, _) =>
              !firstMultiset.get.contains(key)
            }))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        val size = s.values.sum
        ans += CEMultiset(n, BigInt(size), s, typ)
    }
    ans
  }

  def detASTTypeFromString(typ: String): Option[Type] = {
    typ match {
      case "Int" => Some(ast.Int)
      case "Bool" => Some(ast.Bool)
      case "Perm" => Some(ast.Perm)
      case "Ref" => Some(ast.Ref)
      case _ => None
    }
  }

  // "buildNewModel" builds takes the CE model from Boogie and transforms it into a model which makes it easier to determine the individual values
  def buildNewModel(originalEntries: Map[String, ModelEntry]): Map[Seq[String], String] = {
    var newEntriesMapping = Map[Seq[String], String]()
    for ((key, value) <- originalEntries) {
      if (value.isInstanceOf[ConstantEntry]) {
        val valConstEntry = value.asInstanceOf[ConstantEntry]
        newEntriesMapping += (Seq(key) -> valConstEntry.toString)
      } else if (value.isInstanceOf[MapEntry]) {
        val tempMapping = value.asInstanceOf[MapEntry].options
        for ((keyTM, valueTM) <- tempMapping) {
          val tempSeq = (keyTM.map(x => x.toString))
          if (tempSeq.contains("else")) {
            //
          } else {
            newEntriesMapping += (Seq(key) ++ tempSeq -> valueTM.toString)
          }
        }
      } else if (value.isInstanceOf[ApplicationEntry]) {
        val applEntry = value.asInstanceOf[ApplicationEntry]
        newEntriesMapping += (Seq(key) -> applEntry.toString)
      } else if (value.toString != UnspecifiedEntry.toString) {
        println("error in buildNewModel")
      }
    }
    newEntriesMapping
  }

  // determine the identifier for the different Heap and Mask instances
  def oldAndReturnHeapMask(workingModel: Map[Seq[String], String], labels: Seq[Declaration]): (Map[String, (String, String)], List[(String, String, String, String)]) = {
    var heapInstances = Set[(String, String)]()
    var maskInstances = Set[(String, String)]()
    var states = Set[(String, String)]()
    for ((k, v) <- workingModel) {
      if (k(0).startsWith("Heap@@")) {
        heapInstances += ((k(0), v))
      } else if (k(0).startsWith("Mask@@")) {
        maskInstances += ((k(0), v))
      } else if (k(0).startsWith("Heap@")) {
        heapInstances += ((k(0), v))
      } else if (k(0).startsWith("Mask@")) {
        maskInstances += ((k(0), v))
      } else if (k(0).startsWith("QPMask@")) {
        maskInstances += ((k(0).stripPrefix("QP").trim, v))
      } else if ((k(0) == "state") && (v == "true")) {
        states += ((k(1), k(2)))
      }
    }

    // determine all the heap and mask states (first all, then sorted and then filtered)
    val hmStates = for {
      (heapId, maskId) <- states
      hName <- heapInstances.collect { case (name, id) if id == heapId => name }
      mName <- maskInstances.collect { case (name, id) if id == maskId => name }
    } yield (hName, mName, heapId, maskId)

    val sortedHMStates = hmStates.toList.sortBy {
      case (heapName, maskName, _, _) =>
        if (heapName.startsWith("Heap@@") && maskName.startsWith("Mask@@")) {
          0
        } else if (heapName.startsWith("Heap@@")) {
          val maskValue = maskName.stripPrefix("Mask@").trim.toInt
          maskValue + 1
        } else if (maskName.startsWith("Mask@@")) {
          val heapValue = heapName.stripPrefix("Heap@").trim.toInt
          heapValue + 1
        } else {
          val heapValue = heapName.stripPrefix("Heap@").trim.toInt
          val maskValue = maskName.stripPrefix("Mask@").trim.toInt
          heapValue + maskValue + 2
        }
    }

    val filteredList = sortedHMStates.foldLeft(List.empty[(String, String, String, String)]) {
      case (acc, curr@(h, m, _, _))
        if h.contains("@@") || m.contains("@@") || acc.isEmpty || acc.last._1.contains("@@") || acc.last._2.contains("@@") || (h.stripPrefix("Heap@").trim.toInt >= acc.last._1.stripPrefix("Heap@").trim.toInt && m.stripPrefix("Mask@").trim.toInt >= acc.last._2.stripPrefix("Mask@").trim.toInt) =>
        acc :+ curr
      case (acc, _) =>
        acc
    }

    var labelsHeapMask = Map[String, (String, String)]()
    labelsHeapMask += ("old" -> (filteredList(0)._3, filteredList(0)._4))
    for (l <- labels) {
      l match {
        case ast.Label(n, _) =>
          val lhi = "Label" + n + "Heap"
          val lmi = "Label" + n + "Mask"
          if (workingModel.contains(Seq(lhi)) && workingModel.contains(Seq(lmi))) {
            labelsHeapMask += (n -> (workingModel.get(Seq(lhi)).get, workingModel.get(Seq(lmi)).get))
          }
        case _ => //
      }
    }
    labelsHeapMask += ("return" -> (filteredList(filteredList.length-1)._3, filteredList(filteredList.length-1)._4))

    (labelsHeapMask, filteredList)
  }

  def detHeaps(opMapping: Map[Seq[String], String], hmStates: List[(String, String, String, String)], model: Model, hmLabels: Map[String, (String, String)], program: Program): Seq[(String, BasicHeap)] = {
    var heapOp = Map[Seq[String], String]()
    var maskOp = Map[Seq[String], String]()
    var qpMaskSet = Set[String]()
    for ((key, value) <- opMapping) {
      if (key(0).startsWith("MapType0Select")) {
        heapOp += (key -> value)
      } else if (key(0).startsWith("MapType1Select")) {
        maskOp += (key -> value)
      } else if (key(0).startsWith("QPMask@")) {
        qpMaskSet += value
      }
    }
    var predContentMap = Map[String, Seq[String]]()
    for (predName <- program.predicates.map(x => x.name)) {
      val predEntry = model.entries.get(predName).getOrElse(model.entries.find{ case (x, _) => (x.startsWith(predName ++ "_") && !x.contains("@"))}.getOrElse(ConstantEntry("")))
      if (predEntry.isInstanceOf[MapEntry] && !predEntry.asInstanceOf[MapEntry].options.isEmpty) {
        for ((predContent, predId) <- predEntry.asInstanceOf[MapEntry].options) {
          predContentMap += (predId.toString -> predContent.map(x => x.toString))
        }
      }
    }
//    var mwContentMap = Map[String, Seq[String]]()
//    for (predName <- program.magi.map(x => x.name)) {
//      val predEntry = model.entries.get(predName).getOrElse(model.entries.find { case (x, _) => (x.startsWith(predName ++ "_") && !x.contains("@")) }.getOrElse(ConstantEntry("")))
//      if (predEntry.isInstanceOf[MapEntry] && !predEntry.asInstanceOf[MapEntry].options.isEmpty) {
//        for ((predContent, predId) <- predEntry.asInstanceOf[MapEntry].options) {
//          predContentMap += (predId.toString -> predContent.map(x => x.toString))
//        }
//      }
//    }
    val permMap = model.entries.get("U_2_real").get.asInstanceOf[MapEntry].options
    var res = Seq[(String, BasicHeap)]()
    for ((labelName, (labelHeap, labelMask)) <- hmLabels) {
      var heapEntrySet = Set[BasicHeapEntry]()
      val heapStore = model.entries.get("MapType0Store").get.asInstanceOf[MapEntry].options
      val maskStore = model.entries.get("MapType1Store").get.asInstanceOf[MapEntry].options
      val heapMap = recursiveBuildHeapMask(heapStore, labelHeap, Map.empty)
      val maskMap = recursiveBuildHeapMask(maskStore, labelMask, Map.empty)
      val commonKeys = heapMap.keys.toSet.intersect(maskMap.keys.toSet)
      for (ck <- commonKeys) {
        val value = heapMap.get(ck).get
        val perm = maskMap.get(ck).get
        val tempPerm: Option[Rational] = detHeapEntryPermission(permMap, perm._1)
        val typ: HeapEntryType = detHeapType(model, qpMaskSet, ck(1), perm._2)
        if (typ == FieldType || typ == QPFieldType) {
          heapEntrySet += BasicHeapEntry(Seq(ck(0)), Seq(ck(1)), value._1, tempPerm, typ)
        } else if (typ == PredicateType || typ == QPPredicateType) {
          heapEntrySet += BasicHeapEntry(Seq(ck(0), ck(1)), predContentMap.get(ck(1)).getOrElse(Seq()), value._1, tempPerm, typ)
        } else if (typ == MagicWandType || typ == QPMagicWandType) {
          //TODO
        }
      }
      var startNow = false
      for ((_, _, heapIdentifier, maskIdentifier) <- hmStates.reverse) {
        if (heapIdentifier == labelHeap && maskIdentifier == labelMask) {
          startNow = true
        }
        if (startNow) {
          for ((maskKey, perm) <- maskOp) {
            val maskId = maskKey(1)
            val reference = maskKey(2)
            val field = maskKey(3)
            if (maskId == maskIdentifier) {
              if (!heapEntrySet.exists({
                case bhe =>
                  ((bhe.reference.length > 0) && (bhe.field.length > 0) && (bhe.reference(0) == reference) && (bhe.field(0) == field)) ||
                  ((bhe.reference.length > 1) && (bhe.reference(0) == reference) && (bhe.reference(1) == field))
              //TODO: implement a case for MW
              })) {
                var tempPerm: Option[Rational] = detHeapEntryPermission(permMap, perm)
                val typ: HeapEntryType = detHeapType(model, qpMaskSet, field, maskId)
                if (typ == FieldType || typ == QPFieldType) {
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(v) => heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), v, tempPerm, typ)
                    case None => heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), "#undefined", tempPerm, typ)
                  }
                } else if (typ == PredicateType || typ == QPPredicateType) {
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(v) => heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), v, tempPerm, typ)
                    case None => heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), "#undefined", tempPerm, typ)
                  }
                } else if (typ == MagicWandType || typ == QPMagicWandType) {

                }

              } else {
                heapEntrySet.find(
                  { case bhe => (bhe.het == FieldType || bhe.het == QPFieldType) && (bhe.reference(0) == reference) && (bhe.field(0) == field) && (bhe.valueID == "#undefined") }
                ) match {
                  case Some(v) =>
                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                      case Some(x) =>
                        heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), x, v.perm, v.het)
                        heapEntrySet -= BasicHeapEntry(Seq(reference), Seq(field), "#undefined", v.perm, v.het)
                      case None => //
                    }
                  case None => //
                }
                heapEntrySet.find(
                  { case bhe => (bhe.het == PredicateType || bhe.het == QPPredicateType) && (bhe.reference(0) == reference) && (bhe.reference(1) == field) && (bhe.valueID == "#undefined") }
                ) match {
                  case Some(v) =>
                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                      case Some(x) =>
                        heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), x, v.perm, v.het)
                        heapEntrySet -= BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), "#undefined", v.perm, v.het)
                      case None => //
                    }
                  case None => //
                }
                //TODO: Magic Wands
//                heapEntrySet.find(
//                  { case bhe => (bhe.het == MagicWandType || bhe.het == QPMagicWandType) && (bhe.reference == reference) && (bhe.field == field) && (bhe.valueID == "#undefined") }
//                ) match {
//                  case Some(v) =>
//                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
//                      case Some(x) =>
//                        heapEntrySet += BasicHeapEntry(reference, field, x, v.perm, v.het)
//                        heapEntrySet -= BasicHeapEntry(reference, field, "#undefined", v.perm, v.het)
//                      case None => //
//                    }
//                  case None => //
//                }
              }
            }
          }
        }
      }
      res +:= (labelName, BasicHeap(heapEntrySet))
    }

    res
  }

  def detHeapType(model: Model, qpMaskSet: Set[String], id: String, maskId: String): HeapEntryType = {
    var predIdSet = Set[String]()
    if (model.entries.get("IsPredicateField").get.isInstanceOf[MapEntry]) {
      for ((k, v) <- model.entries.get("IsPredicateField").get.asInstanceOf[MapEntry].options) {
        if (v.toString == "true") {
          predIdSet += k(0).toString
        }
      }
    }
    var mwIdSet = Set[String]()
    if (model.entries.get("IsWandField").get.isInstanceOf[MapEntry]) {
      for ((k, v) <- model.entries.get("IsWandField").get.asInstanceOf[MapEntry].options) {
        if (v.toString == "true") {
          mwIdSet += k(0).toString
        }
      }
    }
    var typ: HeapEntryType = FieldType
    if (predIdSet.contains(id)) {
      if (qpMaskSet.contains(maskId)) {
        typ = QPPredicateType
      } else {
        typ = PredicateType
      }
    } else if (mwIdSet.contains(id)) {
      if (qpMaskSet.contains(maskId)) {
        typ = QPMagicWandType
      } else {
        typ = MagicWandType
      }
    } else {
      if (qpMaskSet.contains(maskId)) {
        typ = QPFieldType
      }
    }
    typ
  }

  def detHeapEntryPermission(permMap: Map[scala.collection.immutable.Seq[ValueEntry], ValueEntry], perm: String): Option[Rational] = {
    for ((s, ve) <- permMap) {
      if (s(0).toString == perm) {
        if (ve.isInstanceOf[ConstantEntry]) {
          return Some(Rational.apply(BigInt(ve.asInstanceOf[ConstantEntry].value.toFloat.toInt), BigInt(1)))
        } else if (ve.isInstanceOf[ApplicationEntry]) {
          val ae = ve.asInstanceOf[ApplicationEntry]
          return Some(Rational.apply(BigInt(ae.arguments(0).asInstanceOf[ConstantEntry].value.toFloat.toInt), BigInt(ae.arguments(1).asInstanceOf[ConstantEntry].value.toFloat.toInt)))
        }
      }
    }
    None
  }

  def recursiveBuildHeapMask(inputMap: Map[scala.collection.immutable.Seq[ValueEntry], ValueEntry], s: String, resultMap: Map[Seq[String], (String, String)]): Map[Seq[String], (String, String)] = {
    val entries: Iterable[(Seq[ValueEntry], ValueEntry)] = inputMap.collect {
      case (key, value) if value.toString == s && key.length >= 3 => (key, value)
    }
    if (entries.isEmpty) {
      return resultMap
    }
    entries.foldLeft (resultMap) {
      case (accMap, (entry, value)) =>
        val newStartString = entry(0)
        val newKey = entry.tail.init.map(x => x.toString)
        var newResultMap = accMap
        if (!accMap.contains(newKey)) {
          newResultMap += (newKey -> (entry.last.toString, value.toString))
        }
        recursiveBuildHeapMask(inputMap, newStartString.toString, newResultMap)
    }
  }

  /**
   * extracts domains from a program. only the ones that are used in the program... no generics
   * it also extracts all instances (translates the generics to concrete values)
   */
  def getAllDomains(model: Model, program: ast.Program): Seq[BasicDomainEntry] = {
//    var domains = Seq[ast.Domain]()
//    var concreteDomains = Seq[(String, Map[ast.TypeVar, Type])]()
//    for (el <- program) {
//      el match {
//        case d: ast.Domain => domains +:= d
//        case ast.DomainType(name, map) =>
//          if (!map.values.toSeq.exists(x => x.isInstanceOf[ast.TypeVar])) {
//            concreteDomains +:= (name, map)
//          }
//        case ast.DomainFuncApp(name, _, map) =>
//          if (!map.values.toSeq.exists(x => x.isInstanceOf[ast.TypeVar])) {
//            concreteDomains +:= (name, map)
//          }
//        case _ => //
//      }
//    }
//    val doms: Seq[(ast.Domain, Map[ast.TypeVar, Type])] = domains.flatMap(x =>
//      if (x.typVars == Nil) {
//        Seq((x, Map.empty[ast.TypeVar, ast.Type]))
//      } else {
//        concreteDomains.filter(_._1 == x.name).map(y => (x, y._2))
//      })
//    println(concreteDomains.toString())
//    println(doms.toString())
//    var domainEntries = Seq[BasicDomainEntry]()
//    for ((dom, typeMap) <- doms) {
//      val types = try {
//        dom.typVars.map(typeMap)
//      } catch {
//        case _: Throwable => Seq()
//      }
//      val translatedFunctions = dom.functions.map(y => detFunction(model, y, typeMap, program))
//      BasicDomainEntry(dom.name, types, translatedFunctions)
//    }
//    domainEntries
    val domains = program.collect {
      case a: ast.Domain => a
    }
    val concreteDoms = program.collect { // find all definitive type instances
      case ast.DomainType(n, map) => (n, map)
      case d: ast.DomainFuncApp => (d.domainName, d.typVarMap) // sometimes we use a function without having an actual member of this...

    }.filterNot(x => containsTypeVar(x._2.values.toSeq)).toSet // make sure we have all possible mappings without duplicates

    val doms = domains.flatMap(x => if (x.typVars == Nil) Seq((x, Map.empty[ast.TypeVar, ast.Type])) else concreteDoms.filter(_._1 == x.name).map(y => (x, y._2))) // changing the typevars to the actual ones

    doms.map(x => {
      val types = try {
        x._1.typVars.map(x._2)
      } catch {
        case _: Throwable => Seq()
      }
      val translatedFunctions = x._1.functions.map(y => detFunction(model, y, x._2, program, false))
      BasicDomainEntry(x._1.name, types, translatedFunctions)
    }).toSeq
  }

  def containsTypeVar(s: Seq[ast.Type]): Boolean = s.exists(x => x.isInstanceOf[ast.TypeVar])

  // extract all non domain internal functions
  def getAllFunctions(model: Model, program: ast.Program): Seq[BasicFunction] = {
    val funcs = program.collect {
      case f: ast.Function => f
    }
    funcs.map(x => detFunction(model, x, Map.empty, program, true)).toSeq
  }

  /**
   * extracts the function instances by searching for the most likely match translating the values in the internal rep
   *
   * @param model
   * @param func   the function to translate
   * @param genmap map of generic types to concrete types
   * @return
   */
  def detFunction(model: Model, func: ast.FuncLike, genmap: Map[ast.TypeVar, ast.Type], program: ast.Program, hd: Boolean): BasicFunction = {
    val fname = func.name
    val resTyp: ast.Type = func.typ
    val argTyp: Seq[ast.Type] = func.formalArgs.map(x => x.typ)
    model.entries.get(fname) match {
      case Some(MapEntry(m, els)) =>
        var options = Map[Seq[String], String]()
        if (hd)  {
          for ((k, v) <- m) {
            options += (k.map(x => x.toString) -> v.toString)
          }
        } else {
          for ((k, v) <- m) {
            options += (k.tail.map(x => x.toString) -> v.toString)
          }
        }
        BasicFunction(fname, argTyp, resTyp, options, els.toString)
      case Some(ConstantEntry(t)) => BasicFunction(fname, argTyp, resTyp, Map.empty, t)
      case Some(ApplicationEntry(n, args)) => BasicFunction(fname, argTyp, resTyp, Map.empty, ApplicationEntry(n, args).toString)
      case Some(x) => BasicFunction(fname, argTyp, resTyp, Map.empty, x.toString)
      case None => BasicFunction(fname, argTyp, resTyp, Map.empty, "#undefined")
    }
  }

}

object CounterexampleGenerator {
  def detStore(store: Seq[Declaration], variables: Seq[CEVariable], collections: Set[CEValue]): StoreCounterexample = {
    var ans = Seq[StoreEntry]()
    for (k <- store) {
      if (k.isInstanceOf[ast.LocalVarDecl]) {
        val v = k.asInstanceOf[ast.LocalVarDecl]
        for (vari <- variables) {
          if (v.name == vari.name) {
            var found = false
            for (coll <- collections) {
              if (vari.entryValue.toString == coll.id) {
                ans +:= StoreEntry(ast.LocalVar(v.name, v.typ)(), coll)
                found = true
              }
            }
            if (!found) {
              ans +:= StoreEntry(ast.LocalVar(v.name, v.typ)(), vari)
            }
          }
        }
      }
    }
    StoreCounterexample(ans)
  }

  def detHeap(opMapping: Map[Seq[String], String], basicHeap: BasicHeap, program: Program, collections: Set[CEValue]): HeapCounterexample = {
    // choosing all the needed values from the Boogie Model
    var usedIdent = Map[String, Member]()
    for ((key, value) <- opMapping) {
      for (fie <- program.fields) {
        if (key(0) == fie.name || (key(0).startsWith(fie.name ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> fie)
        }
      }
      for (pred <- program.predicates) {
        if (key(0) == pred.name || (key(0).startsWith(pred.name ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> pred)
        }
      }
//      for ((interName, origName) <- mwNamesMap) {
//        if (key(0) == interName) {
//          usedIdent += (value -> (Seq(origName) ++ key.tail).toString())
//        }
//      }
    }

    var ans = Seq[(Member, FinalHeapEntry)]()
    var tempOld = Set[(String, String, String, String)]()
    var tempRef = Map[String, String]()
    var added = false
    for (bhe <- basicHeap.basicHeapEntries) {
      bhe.het match {
        case FieldType | QPFieldType=>
          usedIdent.get(bhe.field(0)) match {
            case Some(f) =>
              val fi = f.asInstanceOf[Field]
              var found = false
              for (coll <- collections) {
                if (bhe.valueID == coll.id) {
                  ans +:= (fi, FieldFinalEntry(bhe.reference(0), fi.name, coll, bhe.perm, fi.typ))
                  found = true
                }
              }
              if (!found) {
                ans +:= (fi, FieldFinalEntry(bhe.reference(0), fi.name, CEVariable("FieldAccessVariable", ConstantEntry(bhe.valueID), Some(fi.typ)), bhe.perm, fi.typ))
              }
            case None => println(s"Could not find a field node for: ${bhe.toString}")
          }
        case PredicateType | QPPredicateType =>
          usedIdent.get(bhe.reference(1)) match {
            case Some(p) =>
              val pr = p.asInstanceOf[Predicate]
              ans +:= (pr, PredFinalEntry(pr.name, bhe.field, bhe.perm))
            case None => println(s"Could not find a predicate node for: ${bhe.toString}")
          }
        case _ => println("This type of heap entry could not be matched correctly!")
      }


      //      usedIdent.get(bhe.reference) match {
      //
      //        case Some(x) =>
      //          if (b)
      //          var found = false
      //          for ((refName, refValue) <- members) {
      //            if (refValue == reference) {
      //              found = true
      //              mappedNames += (refName ++ "." ++ usedIdent.get(field).get -> (value, permission))
      //              if (bhe.value.startsWith("T@U!val!")) {
      //                tempRef += (bhe.value -> (refName ++ "." ++ usedIdent.get(field).get))
      //                added = true
      //              }
      //            }
      //          }
      //          if (!found) {
      //            tempOld += ((reference, field, value, permission))
      //          }
      //      }
      //    }
      //    while (added) {
      //      added = false
      //      for ((reference, field, value, permission) <- tempOld) {
      //        tempRef.get(reference) match {
      //          case Some(x) =>
      //            tempOld -= ((reference, field, value, permission))
      //            mappedNames += (x ++ "." ++ usedIdent.get(field).get -> (value, permission))
      //            if (value.startsWith("T@U!val!")) {
      //              tempRef += (value -> (x ++ "." ++ usedIdent.get(field).get))
      //              added = true
      //            }
      //          case None => //
      //        }
      //      }
      //    }
    }
    HeapCounterexample(ans)
  }
}


/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample.
  */
object BoogieModelTransformer {

  /**
    * Adds a counterexample to the given error if one is available.
    */
  def transformCounterexample(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]): Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError].methodIdentifier)) {
      val ce = CounterexampleGenerator(e, names, program, wandNames)
      println(ce.toString)
      val finalModel = Map[String, ModelEntry]()
//      for ((k, v) <- e.asInstanceOf[VerificationError].failureContexts(0).counterExample.get.model.entries)
//        println(k.toString ++ " --> " ++ v.toString)
      val model = Model(finalModel)
      println("Model:")
      //println(model)
      e.asInstanceOf[VerificationError].failureContexts = scala.collection.immutable.Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
    }
  }

  // a CE generator for functions
  def detFunc(opMapping: Map[Seq[String], String], hmStates: List[(String, String, String, String)]): Map[Seq[String], String] = {
    var retMap = Map[Seq[String], String]()
    for ((_, _, hi, _) <- hmStates.reverse) {
      for ((k, v) <- opMapping) {
        if (k(1) == hi) {
          if (!retMap.contains(Seq(k(0))++k.tail.tail)) {
            retMap += ((Seq(k(0))++k.tail.tail) -> v)
          }
        }
      }
    }
    retMap
  }

  def prepareMWnames(mwNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]): Map[String, String] = {
    var res = Map[String, String]()
    mwNames match {
      case Some(mapping) =>
        for ((origName, interName) <- mapping) {
          res += (interName.name.name -> origName.toString())
        }
      case None => //
    }
    res
  }

}

sealed trait HeapEntryType
case object FieldType extends HeapEntryType
case object PredicateType extends HeapEntryType
case object QPFieldType extends HeapEntryType
case object QPPredicateType extends HeapEntryType
case object MagicWandType extends HeapEntryType
case object QPMagicWandType extends HeapEntryType

/*
  Helper class for permissions
 */

final class Rational(n: BigInt, d: BigInt) extends Ordered[Rational] {
  require(d != 0, "Denominator of Rational must not be 0.")

  private val g = n.gcd(d)
  val numerator: BigInt = n / g * d.signum
  val denominator: BigInt = d.abs / g

  def +(that: Rational): Rational = {
    val newNum = this.numerator * that.denominator + that.numerator * this.denominator
    val newDen = this.denominator * that.denominator
    Rational(newNum, newDen)
  }
  def -(that: Rational): Rational = this + (-that)
  def unary_- = Rational(-numerator, denominator)
  def abs = Rational(numerator.abs, denominator)
  def signum = Rational(numerator.signum, 1)

  def *(that: Rational): Rational = Rational(this.numerator * that.numerator, this.denominator * that.denominator)
  def /(that: Rational): Rational = this * that.inverse
  def inverse = Rational(denominator, numerator)

  def compare(that: Rational) = (this.numerator * that.denominator - that.numerator * this.denominator).signum

  override def equals(obj: Any) = obj match {
    case that: Rational => this.numerator == that.numerator && this.denominator == that.denominator
    case _ => false
  }

  override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(n, d)

  override lazy val toString = s"$numerator/$denominator"
}

object Rational extends ((BigInt, BigInt) => Rational) {
  val zero = Rational(0, 1)
  val one = Rational(1, 1)

  def apply(numer: BigInt, denom: BigInt) = new Rational(numer, denom)
  def unapply(r: Rational) = Some(r.numerator, r.denominator)
}