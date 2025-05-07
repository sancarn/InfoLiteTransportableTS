import * as zip from "@zip.js/zip.js";
import TransportableEntryTypes from "./InfoLiteEntryTypes.json" assert { type: "json" };
import TransportableVersions from "./InfoLiteTransportableVersions.json" assert { type: "json" };

export type IInfoLiteZip = {
  file: zip.ZipReader<zip.BlobReader>;
  entries: zip.Entry[];
};
export type IConstructorArguments = {
  file: File;
  zip: IInfoLiteZip;
  parsedEntries: ITransportableEntryData[];
};

/**
 * A high level interface containing core information about a transportable entry / model object.
 * Additionally this interface contains the hierarchy of child entries.
 */
export type ITransportableEntry = {
  name: string;
  type: string;
  path: string;
  depth: number;
  data: ITransportableEntryData;
  children: ITransportableEntry[];
};

/**
 * A map of data for a transportable entry. Includes the entry's internal ID, icon, a zip entry, and metadata.
 */
export type ITransportableEntryData = {
  id: number | null;
  type: string;
  icon: string;
  zipEntry: zip.Entry;
  isDeleted: boolean;
  data: ITransportableEntryMetaData;
};

/**
 * A map of metadata for a transportable entry.
 */
export type ITransportableEntryMetaData = {
  [key: string]: string;
};

/**
 * An interface wrapping items of `InfoLiteEntryTypes.json`.
 */
export type ITransportableEntryType = {
  type: string;
  id: number | null;
  icon: string;
};

/**
 * A validation error represents a mismatch between an expected node from a DSL schema
 * and an actual node in the transportable database.
 */
export type IValidationError = {
  expected: IValidationNode | null;
  actual: ITransportableEntry;
  error: {
    id: number;
    message: string;
    type:
      | "actual:self-expected:self" //Expected and actual refer to the same node
      | "actual:child-expected:parent" //Expected refers to the parent node, actual refers to the child node. E.G. Expected child of type [Model Object] - Actual child found was [Model Network]
      | "actual:parent-expected:child"; //Expected refers to the child node, actual refers to the parent node. E.G. Actual child of type [Model Network] found errornously within an expected and successfully matched parent.
  };
};

/**
 * A validation tree node represents a node which is either in or missing from the transportable database
 * and it's corresponding validation errors.
 */
export type IValidationTreeNode =
  | IValidationTreeBasicNode
  | IValidationTreeMissingNode;

/**
 * A validation tree node represents a node in the transportable database and it's corresponding validation errors.
 */
export type IValidationTreeBasicNode = {
  validationType: "basic";
  errors: IValidationError[];
  children: IValidationTreeNode[];
} & ITransportableEntry;

/**
 * A missing child node represents a node in the transportable database which was expected but not found.
 */
export type IValidationTreeMissingNode = {
  validationType: "missing-child";
  errors: IValidationError[];
  children: IValidationTreeNode[];
};

/**
 * A validation result represents the result of validating a transportable database against a DSL schema.
 */
export type IValidationResult =
  | {
      type: "success";
      tree: IValidationTreeNode;
    }
  | {
      type: "error";
      errors: IValidationError[];
      tree: IValidationTreeNode;
    };

/**
 * A map of variables that can be used in the DSL string.
 *
 * Variables are utilised in a DSL using the syntax `${variableName}` and can be used to match standard patterns in the DSL string.
 * For example, the following DSL string uses the variable `id` to match a pattern that matches any integer:
 * parseDSL("|- 1# [ModelObject] /Model $id/", {"id": /\d+/})  ==> "|- 1# [ModelObject] /Model \d+/"
 */
export type IValidationVariables = {
  [key: string]: RegExp;
};

/**
 * A validation node represents a part of the DSL string.
 */
export type IValidationNode = {
  type: string;
  min: number;
  max: number;
  name: RegExp | null;
  children: IValidationNode[];
  lineNumber?: number;
  skipDescendants?: boolean;
};

/**
 * A validation token represents a single line in the DSL string.
 */
export type IValidationToken = {
  depth: number;
  node: IValidationNode;
};

/**
 * Parses a zip entry in the InfoLite transportable database.
 * @param entry - The zip entry to parse.
 * @returns - A Promise that resolves to the parsed entry data.
 * @remarks - Each model object .DAT file contains metadata for the model object e.g.
 *     IWTDB002
 *     #Children,1,(391)
 *     #Parent,1,433
 *     #UsedBy,1,()
 *     #Uses,1,()
 *     Comment,0,
 *     CreationGUID,1,{771A82DB-B27B-4236-9A53-DD5638D4A3EA}
 *     Hidden,0,
 *     ID,1,1
 *     Master Group,1,1
 *     ModificationGUID,1,{771A82DB-B27B-4236-9A53-DD5638D4A3EA}
 *     ModifiedBy,1,jwa
 *     Name,1,My Distribution network
 *     NoInheritUserRoles,0,
 *     Parent,0,
 *     RecycledBy,0,
 *     RecycleParent,0,
 *     RecycleParentType,0,
 *     WhenCreated,1,43403.58208333
 *     WhenModified,1,43403.58208333
 *     WhenRecycled,0,
 */
async function parseEntry(entry: zip.Entry): Promise<ITransportableEntryData> {
  return new Promise(async (resolve, reject) => {
    let fileName = entry.filename;

    let id: number | null = null;
    let type = "";
    let icon = "";
    let isDeleted = false;
    if (fileName.match(/RootObjects\.dat/i)) {
      id = 0;
      type = "Root";
      icon = "";
    } else if (fileName.match(/Globals\.dat/i)) {
      id = -1;
      type = "DB:Globals";
      icon = "";
    } else {
      let parts = fileName.match(
        /^(?<typeID>[A-Z]+?)(?<deleted>XXX)?(?<cumulativeID>\d+)\.DAT$/
      );
      isDeleted = parts?.groups?.deleted === "XXX";
      let cumulativeID = parseInt(parts?.groups?.cumulativeID || "0", 10);
      let typeData = TransportableEntryTypes[
        parts?.groups?.typeID || "Unknown"
      ] as ITransportableEntryType;
      if (!typeData)
        throw new Error(`Unknown typeID: ${parts?.groups?.typeID}`);
      if (typeData.id != null) {
        id = typeData.id + cumulativeID * 256;
      } else {
        id = null;
      }
      type = typeData.type;
      icon = typeData.icon;
    }

    //Obtain file content
    let writer = new zip.TextWriter();
    if (!entry?.getData) {
      reject(new Error("Entry or entry.getData is undefined."));
      return;
    }
    let text = await entry.getData(writer).catch((error) => {
      reject(new Error("Error getting data from entry: " + error));
    });
    if (!text) {
      reject(
        new Error(
          "Error getting data from entry: No text returned from entry " +
            entry.filename
        )
      );
      return;
    }
    let data = text.split(/\r?\n/).reduce((acc, line) => {
      let match = line.match(
        /^\s*(?<name>[^,]+),\s*(?<valid>[01]),\s*(?<value>.*)$/
      );
      if (match) {
        if (match.groups?.valid === "1") {
          acc[match.groups?.name] = match.groups?.value;
        }
      }
      return acc;
    }, {});
    resolve({
      id,
      type,
      icon,
      isDeleted,
      zipEntry: entry,
      data,
    } as ITransportableEntryData);
  });
}

//Zip entries in the form:
// ZipRoot
// |- numbatdata    -|
// |  |- s100-1.wdb  |
// |  |- s102-1.wdb  | - binary data - ignore
// |  |- s102-2.wdb  |
// |  |- ...        -|
// |
// |- Globals.Dat     - Transportable Metadata
// |- RootObjects.Dat - Root object ids and recycling bin ids

// |- AG1.DAT       -|
// |- AG2.DAT        |- asset groups and model objects
// |- AG3.DAT       -|
// |- ...
// |- WKSP1.DAT                    - model object
// |- WKSP1Collection Network.DAT  - WKSP1 model object metadata
// |- GM1.DAT                      - model object
// |- GM1.tin                      - GM1 model object metadata
// |- AGXXX7.DAT                   -|
// |- AGXXX28.DAT                  -|- Deleted objects (There is no AG7.DAT or AG28.DAT)

/**
 * A class for working with InfoLite transportable databases.
 */
export default class InfoLiteTransportable {
  /**
   * Tests if a file is a valid InfoLite transportable database.
   * @param file - The file to test.
   * @returns - A boolean indicating whether the file is a valid InfoLite transportable database.
   */
  static TestFile(file: File): boolean {
    return file.name.endsWith(".icmt");
  }

  /**
   * Creates a new instance of the InfoLiteTransportable class from an ArrayBuffer.
   * @param buffer - The ArrayBuffer to create the instance from.
   * @returns - A Promise that resolves to the new instance of the InfoLiteTransportable class.
   */
  static async CreateFromArrayBuffer(
    buffer: ArrayBuffer
  ): Promise<InfoLiteTransportable> {
    const blob = new Blob([buffer]);
    return await InfoLiteTransportable.CreateFromFile(blob as File, true);
  }

  /**
   * Creates a new instance of the InfoLiteTransportable class from a icmt file.
   * @param file - The file to create the instance from.
   * @param force - A boolean indicating whether to force the creation of the instance even if the file does not have a valid InfoLite transportable database extension.
   * @returns - A Promise that resolves to the new instance of the InfoLiteTransportable class.
   */
  static async CreateFromFile(
    file: File,
    force: Boolean
  ): Promise<InfoLiteTransportable> {
    if (!file) {
      throw new Error("File is required.");
    }
    if (file.size === 0) {
      throw new Error("File is empty.");
    }
    if (!InfoLiteTransportable.TestFile(file) && !force) {
      throw new Error("Invalid file type. Expected .icmt file.");
    }
    let oZIP = new zip.ZipReader(new zip.BlobReader(file));
    let entries = await oZIP.getEntries();
    if (entries.length === 0) {
      throw new Error(
        "No entries found in the transportable database. Invalid."
      );
    }
    let parsedEntries = (
      await Promise.all(
        entries.map(async (entry) => {
          if (
            !entry.directory &&
            entry.filename.match(
              /^(?:(?:\w+?\d+\.DAT)|(?:RootObjects\.DAT)|(?:Globals\.DAT))$/i
            )
          ) {
            return await parseEntry(entry);
          } else {
            return null;
          }
        })
      )
    ).filter((entry) => entry != null);

    return new InfoLiteTransportable({
      file,
      zip: { file: oZIP, entries },
      parsedEntries,
    });
  }

  file: File;
  zip: IInfoLiteZip;
  root: ITransportableEntry | null = null;
  deleted: ITransportableEntry[] = [];
  globals: ITransportableEntryMetaData | undefined;

  /**
   * Creates a new instance of the InfoLiteTransportable class.
   * @param data - The constructor arguments.
   */
  constructor(data: IConstructorArguments) {
    console.log({ constructorData: data });
    this.file = data.file;
    this.zip = data.zip;

    let globals = data.parsedEntries.find((e) => e.type == "DB:Globals");
    let root = data.parsedEntries.find((e) => e.type == "Root");
    let rest = data.parsedEntries.filter(
      (e) => !["Root", "DB:Globals"].includes(e.type)
    );

    this.globals = globals?.data;

    if (!root) throw new Error("No Root entry found.");
    this.root = {
      name: "Root",
      type: "Root",
      path: ">Root",
      depth: 0,
      data: root,
      children: [],
    };

    //Convert this.root into a tree
    let entryStore = {
      "0": this.root,
    };
    rest.forEach((entry) => {
      let id = entry.id;
      if (id != null) {
        entryStore[id.toString()] = {
          name: entry.data.Name,
          type: entry.type,
          data: entry,
          children: [],
        };
      }
    });
    rest.forEach((entry) => {
      if (entry.id == null) return; //Skip null ids

      //Add entry to parent and set path
      const parentMain: ITransportableEntry = entryStore[entry.data["#Parent"]];
      const entryMain: ITransportableEntry = entryStore[entry.id?.toString()];

      //Parent information for deleted entires is wiped, usually these are added to a "Recycle Bin" group. Thusly, we add them to `deleted` array.
      if (entryMain.data.isDeleted) {
        this.deleted.push(entryMain);
      } else {
        parentMain.children.push(entryMain);
      }
    });

    //Recursively set depth and path
    let setDepthAndPath = (
      node: ITransportableEntry,
      path: string = "",
      depth: number = 0
    ) => {
      node.depth = depth;
      node.path = `${path}>[${node.type}] ${node.name}`;
      node.children.forEach((child) => {
        setDepthAndPath(child, node.path, depth + 1);
      });
    };
    setDepthAndPath(this.root);
  }

  /**
   * Converts the transportable database to a DSL string that can be used to validate the database.
   * @returns - A DSL string that describes the structure of the transportable database.
   */
  toValidationDSL(): string {
    let dsl = ["Root"];
    let recurse = (obj, depth) => {
      depth++;
      obj.children.forEach((child) => {
        dsl.push("|  ".repeat(depth) + `|- 1# [${child.type}] /${child.name}/`);
        recurse(child, depth);
      });
    };
    recurse(this.root, 0);
    return dsl.join("\r\n");
  }

  /**
   * Returns the version of the transportable database.
   * @returns - The version of the transportable database. E.G. 9.5.1234
   */
  getVersion(): string {
    return `${TransportableVersions[this.globals?.VersionGUID as string]}.${
      this.globals?.SubVersion
    }`;
  }

  /**
   * Validates the transportable database against a DSL schema.
   * @param dslSchema - A DSL string that describes the expected structure of the transportable database.
   * @param vars - A map of variables that can be used in the DSL string.
   * @returns - A validation result containing the validation tree and a flat array of errors.
   */
  validate(dslSchema: string, vars: IValidationVariables): IValidationResult {
    //Parse DSL
    let dsl = this.parseDSL(dslSchema, vars);

    //Sanity check
    if (this.root == null) throw new Error("Root is null");

    //Clone the tree to avoid mutating the original tree.
    let cloner = (entry: ITransportableEntry): IValidationTreeNode => {
      return {
        ...entry,
        validationType: "basic",
        children: entry.children.map(cloner),
        errors: [],
      } as IValidationTreeBasicNode;
    };
    let tree: IValidationTreeNode = cloner(this.root);

    //Validate the tree
    let errors: IValidationError[] = [];
    const recurse = (
      schemaNode: IValidationNode,
      actualNode: IValidationTreeBasicNode
    ) => {
      //Skip validation on node and all descendants of this node if skipDescendants is set
      if (schemaNode.type === "ANY" && schemaNode.skipDescendants) {
        return;
      }

      // Check type
      if (schemaNode.type !== "ANY" && actualNode.type !== schemaNode.type) {
        let error: IValidationError = {
          expected: schemaNode,
          actual: actualNode,
          error: {
            id: 1,
            message: `Expected type '${schemaNode.type}', got '${actualNode.type}'.`,
            type: "actual:self-expected:self",
          },
        };
        errors.push(error);
        actualNode.errors.push(error);

        //Early return. In an ideal world we would perform a fuzzy match and forward onto matched children.
        //But as it stands, if we don't match this node, all children will flag as "unexpected", which is not very helpful.
        //TODO: Implement fuzzy compare
        return;
      }

      // Report track unexpected children
      const matchedChildren = new Set<IValidationTreeNode>();

      // Validate children against schema
      for (const expectedChild of schemaNode.children) {
        const matches = (
          actualNode.children as IValidationTreeBasicNode[]
        ).filter((child) => {
          const isTypeMatch =
            expectedChild.type === "ANY" || child.type === expectedChild.type;
          const isNameMatch =
            expectedChild.name === null || expectedChild.name.test(child.name);
          return isTypeMatch && isNameMatch;
        });

        //Track matched children
        matches.forEach((match) => matchedChildren.add(match));
        if (matches.length < expectedChild.min) {
          let error: IValidationError = {
            expected: expectedChild,
            actual: actualNode,
            error: {
              id: 2,
              message: `Expected at least ${expectedChild.min} child(ren) of type [${expectedChild.type}] matching ${expectedChild.name}, found ${matches.length}.`,
              type: "actual:parent-expected:child",
            },
          };
          errors.push(error);

          //Add missing child error to actual node
          actualNode.children.unshift({
            validationType: "missing-child",
            errors: [error],
            children: [],
          });
        }
        if (matches.length > expectedChild.max) {
          const excessMatches = matches.slice(expectedChild.max);
          for (const child of excessMatches) {
            let error: IValidationError = {
              expected: expectedChild,
              actual: child,
              error: {
                id: 3,
                message: `Exceeded maximum of ${expectedChild.max} allowed [${expectedChild.type}] child(ren) matching ${expectedChild.name}.`,
                type: "actual:parent-expected:child",
              },
            };
            errors.push(error);
            child.errors.push(error);
          }
        }

        // Recurse into each matched child
        if (matches.length >= expectedChild.min) {
          matches.forEach((match) => {
            recurse(expectedChild, match);
          });
        }
      }

      // Report unexpected children
      const unexpectedChildren = actualNode.children
        .filter((node) => node.validationType == "basic") //Only include basic nodes
        .filter((child) => !matchedChildren.has(child));
      unexpectedChildren.forEach((child) => {
        let error: IValidationError = {
          expected: schemaNode,
          actual: child,
          error: {
            id: 4,
            message: `Unexpected child "[${child.type}] ${child.name}" of parent "[${actualNode.type}] ${actualNode.name}".`,
            type: "actual:child-expected:parent",
          },
        };
        errors.push(error);
        child.errors.push(error);
      });
    };

    recurse(dsl, tree as IValidationTreeBasicNode);

    return errors.length > 0
      ? { type: "error", tree, errors }
      : { type: "success", tree };
  }

  /**
   * Preprocesses the DSL string by replacing variables with their corresponding regular expressions.
   * @param dsl - The DSL string to be preprocessed.
   * @param vars - The variables to be replaced.
   * @returns - The preprocessed DSL string.
   */
  private preprocessVars(dsl: string, vars: IValidationVariables) {
    let processed = dsl;
    for (const [key, regex] of Object.entries(vars)) {
      const pattern = regex.toString().slice(1, -1); // remove leading and trailing /
      processed = processed.replace(new RegExp(`\\$${key}`, "g"), pattern);
    }
    return processed;
  }

  /**
   * Parses the DSL string and returns a validation tree.
   * @param dsl - The DSL string to be parsed.
   * @param vars - The variables to be used in the DSL string.
   * @returns - The validation tree.
   */
  private parseDSL(dsl: string, vars: IValidationVariables = {}) {
    dsl = this.preprocessVars(dsl.trim(), vars);

    const lines = dsl
      .split("\n")
      .map((line) => line.trim())
      .filter(Boolean);

    const root: IValidationNode = {
      type: "Root",
      name: /Root/,
      min: 1,
      max: 1,
      children: [],
    };
    const tokens: IValidationToken[] = lines
      .slice(1)
      .map((line, index) => this.parseDSLLine(line, index + 2)); //+2 because we skip the root line

    const stack = [{ node: root, depth: -1 }];

    for (const token of tokens) {
      while (stack.length && stack[stack.length - 1].depth >= token.depth) {
        stack.pop();
      }
      const parent = stack[stack.length - 1].node;
      parent.children.push(token.node);
      stack.push({ node: token.node, depth: token.depth });
    }
    return root;
  }

  /**
   * Parses a single line of the DSL string and returns a validation token.
   * @param line - The line of the DSL string to be parsed.
   * @param lineNumber - The line number of the DSL string.
   * @returns - The validation token.
   */
  private parseDSLLine(line: string, lineNumber: number): IValidationToken {
    const depth = (line.match(/\|/g) || []).length;
    let clean = line.match(/\|- (.*)/)?.[1].trim();
    if (clean == null) throw Error(`DSL line has incorrect syntax "${line}"`);

    switch (clean) {
      case "Root":
        return {
          depth,
          node: {
            type: "Root",
            name: null,
            min: 1,
            max: 1,
            children: [],
            lineNumber,
          },
        };
      case "*":
        return {
          depth,
          node: {
            type: "ANY",
            name: /.*/,
            min: 0,
            max: Infinity,
            children: [],
            lineNumber,
          },
        };
      case "**":
        return {
          depth,
          node: {
            type: "ANY",
            name: /.*/,
            min: 0,
            max: Infinity,
            children: [],
            lineNumber,
            skipDescendants: true, //Skip all descendants of this node
          },
        };
    }

    const data = clean.match(
      /\s*(?<count>\d+\+?|\d+-\d+)?#\s+\[(?<type>[^\]]*)]\s+(?<pattern>\/(?:\\\/|[^\/])*\/i?)/
    );
    if (data == null) throw new Error(`Invalid line: '${clean}'`);

    type IData = { count: string; type: string; pattern: string };
    const { count, type, pattern } = data.groups as IData;

    const regexParts = pattern.match(
      /\/(?<regexPattern>(?:\\\/|[^\/])*)\/(?<regexFlags>[iuA]*)/ //A is a custom flag for unanchoring the regex. All regexes will be anchored by default.
    );
    if (regexParts == null)
      throw new Error(
        `Invalid pattern found in line "${lineNumber}" of Validation DSL: '${pattern}'`
      );
    //@ts-ignore
    let { regexPattern, regexFlags } = regexParts.groups;

    //Anchoring regex by default
    if (!regexFlags.includes("A")) {
      regexPattern = `^${regexPattern}$`;
    } else {
      //RegExp will throw if flag A is passed, so remove it
      regexFlags = regexFlags.replace("A", "");
    }

    //Creawte regex matcher for name
    const regexNameMatcher = new RegExp(regexPattern, regexFlags);

    //Parse count to min/max format
    let min = 0;
    let max = 0;
    if (count) {
      if (count.includes("-")) {
        const parts = count.split("-");
        min = parseInt(parts[0], 10);
        max = parseInt(parts[1], 10);
      } else if (count.includes("+")) {
        const parts = count.split("+");
        min = parseInt(parts[0], 10);
        max = Infinity;
      } else {
        min = parseInt(count, 10);
        max = min;
      }
    } else {
      min = 1;
      max = 1;
    }
    return {
      depth,
      node: {
        type,
        min,
        max,
        name: regexNameMatcher,
        children: [],
        lineNumber,
      },
    };
  }
}

export function validationResultsToString(result: IValidationResult): string {
  let lines: string[] = [];
  let recurse = (
    node: IValidationTreeNode,
    depth: number,
    hasInheritedError: boolean = false
  ) => {
    const indent = "|  ".repeat(depth);
    if (node.validationType === "basic") {
      const label = `[${node.type}] ${node.name}`;
      const isDirectError = node.errors.length > 0;

      let status = "✅"; //Assume correct
      if (hasInheritedError) status = "🟤";
      if (isDirectError) status = "⛔";

      if (node.errors.length == 1) {
        //Print inline error
        lines.push(
          `${status} ${indent}|- ${label} ::: ${node.errors[0].error.message}`
        );
      } else if (node.errors.length > 1) {
        //Print errors as children
        for (const error of node.errors) {
          lines.push(`${status} ${indent}|- ${label}`);
          lines.push(`${status} ${indent}|  |- ${error.error.message}`);
        }
      } else if (hasInheritedError) {
        //Print node with error message "(inherited)"
        lines.push(
          `${status} ${indent}|- ${label} ::: (inherited from parent)`
        );
      } else {
        //Print node with no error message
        lines.push(`${status} ${indent}|- ${label}`);
      }
      node.children.forEach((child) => {
        recurse(child, depth + 1, isDirectError || hasInheritedError);
      });
    } else {
      //Print missing child node
      lines.push(
        `⛔ ${indent}|- [Missing] ::: ${node.errors[0].error.message}`
      );
      for (let i = 1; i < node.errors.length; i++) {
        lines.push(`⛔ ${indent}|  |- ${node.errors[i].error.message}`);
      }
    }
  };
  recurse(result.tree, 0);
  return lines.join("\n");
}
