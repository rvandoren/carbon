package viper.carbon.boogie

import viper.carbon.boogie.IntermediateCounterexampleModel.transformModelEntries

import scala.collection.mutable
import util.control.Breaks._
import viper.carbon.verifier.FailureContextImpl
import viper.silver.ast
import viper.silver.ast.Literal
import viper.silver.verifier.{AbstractError, ApplicationEntry, ConstantEntry, MapEntry, Model, ModelEntry, SimpleCounterexample, UnspecifiedEntry, VerificationError}
import viper.silver.ast.{AbstractLocalVar, Declaration, LocalVar, MagicWandStructure, Program, Type}

class Counterexample {
  val store = Seq[(AbstractLocalVar, CEValue)]()
  //val heaps = Seq[Seq[(Declaration, HeapInstance)]]
  val domains = null
}

sealed trait CEValue

case class CEVariable(name: String, value: ModelEntry, typ: Option[Type]) extends CEValue {
  override lazy val toString = s"Variable Name: ${name}, Value: ${value.toString}, Type: ${typ.toString()}"
}

case class CESequence(name: String, sequence: Seq[String], memberTypes: Option[Type]) extends CEValue {
  override lazy val toString = s"Sequence: $name --> $sequence, Type: Seq($memberTypes)"
}

case class CESet(name: String, set: Set[String], memberTypes: Option[Type]) extends CEValue {
  override lazy val toString = s"Set: $name --> $set, Type: Set($memberTypes)"
}

case class CEMultiset(name: String, set: Set[String], memberTypes: Option[Type]) extends CEValue {
  override lazy val toString = s"Multiset: $name --> $set, Type: Multiset($memberTypes)"
}

case class BasicHeap(basicHeapEntries: Set[BasicHeapEntry])

case class BasicHeapEntry(reference: String, fields: Seq[String], valueID: String, perm: Option[Literal])

case class EvaluatedHeap(finalHeapEntries: Set[FinalHeapEntry])

sealed trait FinalHeapEntry

case class FieldAccess(reference: String, fields: Seq[String], valueID: String, perm: Option[Literal])



case class IntermediateCounterexampleModel(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]) {
  val ve = e.asInstanceOf[VerificationError]
  val errorMethod = ErrorMemberMapping.mapping.get(ve.methodIdentifier).get
  val originalEntries = ve.failureContexts(0).counterExample.get.model
  val typenamesInMethod = names.get(errorMethod.name).get.map(e => e._2 -> e._1)
  val methodVarDecl = program.methodsByName.get(errorMethod.name).get.scopedDecls

  val basicVariables = IntermediateCounterexampleModel.detCEvariables(originalEntries.entries, typenamesInMethod)
  val allSequences = IntermediateCounterexampleModel.detSequences(originalEntries)
  val allSets = IntermediateCounterexampleModel.detSets(originalEntries)
  val allCollections = allSequences ++ allSets
  //lazy val store = null

  val workingModel = IntermediateCounterexampleModel.buildNewModel(originalEntries.entries)
  val hmStates = IntermediateCounterexampleModel.oldAndReturnHeapMask(workingModel)
  val allHeapInstances = IntermediateCounterexampleModel.detHeapTypes(workingModel, hmStates)

  override def toString: String = {
    var finalString = "     Intermediate Counterexampel: \n"
    finalString ++= "Store: \n"
    for (in <- basicVariables)
      finalString ++= (in.toString ++ "\n")
    for (in <- allCollections)
      finalString ++= (in.toString ++ "\n")
    finalString
  }
}


object IntermediateCounterexampleModel {

//  def detBasicVariables(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String], methodVariables: Seq[Declaration]): Seq[CEVariable] = {
//    var res = Seq[CEVariable]()
//    val modelVariables = transformModelEntries(originalEntries, namesInMember)
//    for (decl <- methodVariables) {
//      println(decl.toString)
//      println(decl.getClass)
//      if (decl.isInstanceOf[AbstractLocalVar]) {
//        val alvDecl = decl.asInstanceOf[AbstractLocalVar]
//        modelVariables.get(alvDecl.toString) match {
//          case Some(x) =>
//            var varTyp: Option[Type] = None
//            if (decl.isInstanceOf[LocalVar]) {
//              varTyp = Some(x.asInstanceOf[LocalVar].typ)
//            }
//            if (x.isInstanceOf[ConstantEntry]) {
//              res +:= CEVariable(alvDecl, x, varTyp)
//            } else if (x.isInstanceOf[ApplicationEntry]) {
//              res +:= CEVariable(alvDecl, x, varTyp)
//            } else {
//              println(s"Couldn't find a ConstantEntry or ApplicationEntry for the Variable: ${alvDecl.name}")
//            }
//          case None => println(s"Couldn't find an entry for the Variable: ${alvDecl.name}")
//        }
//      }
//    }
//    res
//  }

  def detCEvariables(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]): Seq[CEVariable] = {
    var res = Seq[CEVariable]()
    val modelVariables = transformModelEntries(originalEntries, namesInMember)
    for ((name, entry) <- modelVariables) {
      //val entryType = detEntryType()
      res +:= CEVariable(name, entry, None)
    }
    res
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
    if (secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1) {
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
  def detSequences(model: Model): Set[CESequence] = {
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
      } else if (opName != "Seq#Singleton" && opName != "Seq#Range" && opName.startsWith("Seq#")) {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    for ((opName, opValues) <- tempMap) {
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
              res += (v -> (x ++ y))
              tempMap -= ((opName, k))
              found = true
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
    var ans = Set[CESequence]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SeqType(x))
          case None => None
        }
        ans += CESequence(n, s, typ)
    }
    ans
  }

  // a CE generator for sets
  def detSets(model: Model): Set[CESet] = {
    var res = Map[String, Set[String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set())
          }
        }
      }
      if (opName == "Set#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
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
    var ans = Set[CESet]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        ans += CESet(n, s, typ)
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
  def oldAndReturnHeapMask(workingModel: Map[Seq[String], String]): List[(String, String, String, String)] = {
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

    filteredList
  }

  def detHeapTypes(opMapping: Map[Seq[String], String], hmStates: List[(String, String, String, String)]): Seq[Set[(String, String, String, String)]] = {
    var permMap = Map[String, String]()
    var heapOp = Map[Seq[String], String]()
    var maskOp = Map[Seq[String], String]()
    for ((key, value) <- opMapping) {
      if (key(0) == "U_2_real") {
        permMap += (key(1) -> value)
      } else if (key(0).startsWith("MapType0Select")) {
        heapOp += (key -> value)
      } else if (key(0).startsWith("MapType1Select")) {
        maskOp += (key -> value)
      }
    }

    var res = Seq[Set[(String, String, String, String)]]()
    for (heapInstance <- 0 to hmStates.length-1) {
      var retSet = Set[(String, String, String, String)]()
      for ((_, _, heapIdentifier, maskIdentifier) <- hmStates.slice(0, heapInstance).reverse) {
        for ((maskKey, perm) <- maskOp) {
          val maskId = maskKey(1)
          val reference = maskKey(2)
          val field = maskKey(3)
          if (maskId == maskIdentifier) {
            if (!retSet.exists({ case (s1, s2, _, _) => (s1 == reference) && (s2 == field) })) {
              heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                case Some(v) => retSet += ((reference, field, v, permMap.get(perm).get))
                case None => retSet += ((reference, field, "#undefined", permMap.get(perm).get))
              }
            } else {
              retSet.find({ case (s1, s2, s3, _) => (s1 == reference) && (s2 == field) && (s3 == "#undefined") }) match {
                case Some(v) =>
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(x) =>
                      retSet += ((reference, field, x, v._4))
                      retSet -= ((reference, field, "#undefined", v._4))
                    case None => //
                  }
                case None => //
              }
            }
          }
        }
      }
      res +:= retSet
    }

//    var oldSet = Set[(String, String, String, String)]()
//    for ((maskKey, perm) <- maskOp) {
//      val maskId = maskKey(1)
//      val reference = maskKey(2)
//      val field = maskKey(3)
//      if (maskId == oldMask) {
//        heapOp.get(Seq("MapType0Select", oldHeap, reference, field)) match {
//          case Some(v) =>
//            oldSet += ((reference, field, v, permMap.get(perm).get))
//          case None =>
//            oldSet += ((reference, field, "#undefined", permMap.get(perm).get))
//        }
//      }
//    }

    res
  }





  // "replaceEntriesModel" choose all the operations for specific type supported in the CE
  def findAllFuncOper(workingModel: Map[Seq[String], String], program: Program): Map[Seq[String], String] = {

    // define output maps for the operations of sequences, sets,
    var funOperations = Map[Seq[String], String]()

    // choose the operations corresponding to the types from the model received by boogie
    for ((k, v) <- workingModel) {
      if (program.functionsByName.keySet.contains(k(0)) || program.domainFunctionsByName.keySet.contains(k(0))) {
        funOperations += (k -> v)
      }
    }

    funOperations
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
      val firstCE = IntermediateCounterexampleModel(e, names, program, wandNames)
      println(firstCE.toString)
      val finalModel = Map[String, ModelEntry]()
      for ((k, v) <- e.asInstanceOf[VerificationError].failureContexts(0).counterExample.get.model.entries)
        println(k.toString ++ " --> " ++ v.toString)
      val model = Model(finalModel)
      println("Model:")
      println(model)


//      println("Old Heap:")
//      for ((reference, field, value, permission) <- oldHeapMap)
//        println(s"Ref: $reference, Field: $field, Value: $value, Perm: $permission")
//      println("Return Heap:")
//      for ((reference, field, value, permission) <- retHeapMap)
//        println(s"Ref: $reference, Field: $field, Value: $value, Perm: $permission")
      // val (evalOldHeap, evalRetHeap) = evaluateHT(workingModel, basicCEheapTypesName, oldHeapMap, retHeapMap, program.predicatesByName.keySet, program.fieldsByName.keySet, prepareMWnames(wandNames))
      //val finalCounterexample = (ceBasicTypes, evalOldHeap, evalRetHeap)
//      println("At old:")
//      for ((name, (value, perm)) <- evalOldHeap)
//        println(s"Name: $name, Value: $value, Perm: $perm")
//      println("On return:")
//      for ((name, (value, perm)) <- evalRetHeap)
//        println(s"Name: $name, Value: $value, Perm: $perm")

      //e.asInstanceOf[VerificationError].failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
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

  def evaluateHT(opMapping: Map[Seq[String], String], members: Map[String, String], oldHeap: Set[(String, String, String, String)], retHeap: Set[(String, String, String, String)], predicates: Set[String], fields: Set[String], mwNamesMap: Map[String, String]): (Map[String, (String, String)], Map[String, (String, String)]) = {
    // choosing all the needed values from the Boogie Model
    var usedIdent = Map[String, String]()
    for ((key, value) <- opMapping) {
      if (key(0) == "null") {
        usedIdent += (value -> "null")
      }
      for ((interName, origName) <- mwNamesMap) {
        if (key(0) == interName) {
          usedIdent += (value -> (Seq(origName) ++ key.tail).toString())
        }
      }
      for (fie <- fields) {
        if (key(0) == fie || (key(0).startsWith(fie ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> fie)
        }
      }
      for (pre <- predicates) {
        if (key(0) == pre) {
          var tempStr = ""
          for ((refName, refValue) <- members) {
            if (key(1) == refValue) {
              tempStr = refName
            }
          }
          for (i <- 2 to key.length-1) {
            breakable {
              for ((refName, refValue) <- members) {
                if (key(i) == refValue) {
                  tempStr += (", " ++ refName)
                  break
                }
              }
              tempStr += (", " ++ key(i))
            }
          }
          usedIdent += (value -> s"$pre($tempStr)")
        }
      }
    }
    // resolve all the names for the Old state
    var mappedNamesOld = Map[String, (String, String)]()
    var tempOld = Set[(String, String, String, String)]()
    var tempRef = Map[String, String]()
    var added = false
    for ((reference, field, value, permission) <- oldHeap) {
      usedIdent.get(reference) match {
        case Some("null") => mappedNamesOld += (usedIdent.get(field).get -> (value, permission))
        case _ =>
          var found = false
          for ((refName, refValue) <- members) {
            if (refValue == reference) {
              found = true
              mappedNamesOld += (refName ++ "." ++ usedIdent.get(field).get -> (value, permission))
              if (value.startsWith("T@U!val!")) {
                tempRef += (value -> (refName ++ "." ++ usedIdent.get(field).get))
                added = true
              }
            }
          }
          if (!found) {
            tempOld += ((reference, field, value, permission))
          }
      }
    }
    while (added) {
      added = false
      for ((reference, field, value, permission) <- tempOld) {
        tempRef.get(reference) match {
          case Some(x) =>
            tempOld -= ((reference, field, value, permission))
            mappedNamesOld += (x ++ "." ++ usedIdent.get(field).get -> (value, permission))
            if (value.startsWith("T@U!val!")) {
              tempRef += (value -> (x ++ "." ++ usedIdent.get(field).get))
              added = true
            }
          case None => //
        }
      }
    }
    // resolve all the names for the Ret state
    var mappedNamesReturn = Map[String, (String, String)]()
    var tempRet = Set[(String, String, String, String)]()
    tempRef = Map.empty[String, String]
    added = false
    for ((reference, field, value, permission) <- retHeap) {
      usedIdent.get(reference) match {
        case Some("null") => mappedNamesReturn += (usedIdent.get(field).get -> (value, permission))
        case _ =>
          var found = false
          for ((refName, refValue) <- members) {
            if (refValue == reference) {
              found = true
              mappedNamesReturn += (refName ++ "." ++ usedIdent.get(field).get -> (value, permission))
              if (value.startsWith("T@U!val!")) {
                tempRef += (value -> (refName ++ "." ++ usedIdent.get(field).get))
                added = true
              }
            }
          }
          if (!found) {
            tempRet += ((reference, field, value, permission))
          }
      }
    }
    while (added) {
      added = false
      for ((reference, field, value, permission) <- tempRet) {
        tempRef.get(reference) match {
          case Some(x) =>
            tempRet -= ((reference, field, value, permission))
            mappedNamesReturn += (x ++ "." ++ usedIdent.get(field).get -> (value, permission))
            if (value.startsWith("T@U!val!")) {
              tempRef += (value -> (x ++ "." ++ usedIdent.get(field).get))
              added = true
            }
          case None => //
        }
      }
    }
    (mappedNamesOld, mappedNamesReturn)
  }

}