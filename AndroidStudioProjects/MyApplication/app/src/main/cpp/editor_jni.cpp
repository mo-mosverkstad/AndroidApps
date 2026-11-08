// JNI bridge for the portable editor core.
//
// Deliberately thin: it converts types, catches C++ exceptions and does
// nothing else. Every decision about documents, undo grouping, carets and
// dirty state lives in native/ where the desktop tests can reach it.
//
// Text crosses the boundary as UTF-16 (jchar == char16_t), so offsets on
// either side refer to the same positions with no conversion.

#include <jni.h>

#include <android/log.h>

#include <exception>
#include <memory>
#include <new>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "editor/editor_model.h"

#define LOG_TAG "EditorCore"
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR, LOG_TAG, __VA_ARGS__)

namespace {

editor::EditorModel* modelFrom(jlong handle) {
    return reinterpret_cast<editor::EditorModel*>(handle);
}

editor::ustring toNative(JNIEnv* env, jstring value) {
    if (value == nullptr) return editor::ustring();
    const jsize length = env->GetStringLength(value);
    editor::ustring out(static_cast<size_t>(length), u'\0');
    if (length > 0) {
        env->GetStringRegion(value, 0, length, reinterpret_cast<jchar*>(&out[0]));
    }
    return out;
}

jstring toJava(JNIEnv* env, const editor::ustring& value) {
    return env->NewString(reinterpret_cast<const jchar*>(value.data()),
                          static_cast<jsize>(value.size()));
}

void throwRuntime(JNIEnv* env, const char* message) {
    LOGE("%s", message);
    if (env->ExceptionCheck()) return;
    jclass cls = env->FindClass("java/lang/RuntimeException");
    if (cls != nullptr) env->ThrowNew(cls, message);
}

}  // namespace

#define GUARD_BEGIN try {
#define GUARD_END(FALLBACK)                        \
    }                                              \
    catch (const std::exception& e) {               \
        throwRuntime(env, e.what());                \
        return FALLBACK;                            \
    }                                               \
    catch (...) {                                   \
        throwRuntime(env, "unknown native error");  \
        return FALLBACK;                            \
    }

#define GUARD_END_VOID                             \
    }                                              \
    catch (const std::exception& e) {               \
        throwRuntime(env, e.what());                \
    }                                               \
    catch (...) {                                   \
        throwRuntime(env, "unknown native error");  \
    }

extern "C" {

JNIEXPORT jlong JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeCreate(JNIEnv* env, jobject) {
    GUARD_BEGIN
    return reinterpret_cast<jlong>(new editor::EditorModel());
    GUARD_END(0)
}

JNIEXPORT void JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeDestroy(JNIEnv* env, jobject, jlong handle) {
    GUARD_BEGIN
    delete modelFrom(handle);
    GUARD_END_VOID
}

// --- tabs ------------------------------------------------------------------

JNIEXPORT jlong JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeCreateTab(JNIEnv* env,
                                                                 jobject,
                                                                 jlong handle,
                                                                 jstring text,
                                                                 jstring fileName,
                                                                 jstring filePath) {
    GUARD_BEGIN
    std::optional<editor::ustring> path;
    if (filePath != nullptr) path = toNative(env, filePath);
    return static_cast<jlong>(modelFrom(handle)->createTab(toNative(env, text),
                                                           toNative(env, fileName),
                                                           std::move(path)));
    GUARD_END(0)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeCloseTab(JNIEnv* env,
                                                                jobject,
                                                                jlong handle,
                                                                jlong tabId) {
    GUARD_BEGIN
    return modelFrom(handle)->closeTab(static_cast<int64_t>(tabId)) ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSelectTab(JNIEnv* env,
                                                                 jobject,
                                                                 jlong handle,
                                                                 jlong tabId) {
    GUARD_BEGIN
    return modelFrom(handle)->selectTab(static_cast<int64_t>(tabId)) ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSetTabFile(JNIEnv* env,
                                                                  jobject,
                                                                  jlong handle,
                                                                  jlong tabId,
                                                                  jstring fileName,
                                                                  jstring filePath) {
    GUARD_BEGIN
    std::optional<editor::ustring> path;
    if (filePath != nullptr) path = toNative(env, filePath);
    return modelFrom(handle)->setTabFile(static_cast<int64_t>(tabId),
                                         toNative(env, fileName),
                                         std::move(path))
               ? JNI_TRUE
               : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeMarkTabSaved(JNIEnv* env,
                                                                    jobject,
                                                                    jlong handle,
                                                                    jlong tabId) {
    GUARD_BEGIN
    return modelFrom(handle)->markTabSaved(static_cast<int64_t>(tabId)) ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeHasUnsavedChanges(JNIEnv* env,
                                                                        jobject,
                                                                        jlong handle) {
    GUARD_BEGIN
    return modelFrom(handle)->hasUnsavedChanges() ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

// --- editing ---------------------------------------------------------------

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSetText(JNIEnv* env,
                                                               jobject,
                                                               jlong handle,
                                                               jstring text,
                                                               jint selectionStart,
                                                               jint selectionEnd) {
    GUARD_BEGIN
    const editor::Selection selection(static_cast<int32_t>(selectionStart),
                                      static_cast<int32_t>(selectionEnd));
    return modelFrom(handle)->setText(toNative(env, text), selection) ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeApplyEdit(JNIEnv* env,
                                                                 jobject,
                                                                 jlong handle,
                                                                 jint pos,
                                                                 jint removeLength,
                                                                 jstring insertText,
                                                                 jint selectionStart,
                                                                 jint selectionEnd) {
    GUARD_BEGIN
    const editor::Selection selection(static_cast<int32_t>(selectionStart),
                                      static_cast<int32_t>(selectionEnd));
    return modelFrom(handle)->applyEdit(static_cast<int32_t>(pos),
                                        static_cast<int32_t>(removeLength),
                                        toNative(env, insertText),
                                        selection)
               ? JNI_TRUE
               : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSetSelection(JNIEnv* env,
                                                                    jobject,
                                                                    jlong handle,
                                                                    jint selectionStart,
                                                                    jint selectionEnd) {
    GUARD_BEGIN
    const editor::Selection selection(static_cast<int32_t>(selectionStart),
                                      static_cast<int32_t>(selectionEnd));
    return modelFrom(handle)->setSelection(selection) ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeUndo(JNIEnv* env, jobject, jlong handle) {
    GUARD_BEGIN
    return modelFrom(handle)->undo() ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT jboolean JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeRedo(JNIEnv* env, jobject, jlong handle) {
    GUARD_BEGIN
    return modelFrom(handle)->redo() ? JNI_TRUE : JNI_FALSE;
    GUARD_END(JNI_FALSE)
}

JNIEXPORT void JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeFinalizeEdits(JNIEnv* env,
                                                                     jobject,
                                                                     jlong handle) {
    GUARD_BEGIN
    modelFrom(handle)->finalizeEdits();
    GUARD_END_VOID
}

// --- reading the snapshot --------------------------------------------------

JNIEXPORT jstring JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeVisibleText(JNIEnv* env,
                                                                   jobject,
                                                                   jlong handle) {
    GUARD_BEGIN
    return toJava(env, modelFrom(handle)->snapshot().text);
    GUARD_END(nullptr)
}

JNIEXPORT jstring JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeActiveText(JNIEnv* env,
                                                                  jobject,
                                                                  jlong handle) {
    GUARD_BEGIN
    return toJava(env, modelFrom(handle)->activeText());
    GUARD_END(nullptr)
}

// [selectedIndex, selectionStart, selectionEnd, canUndo, canRedo, tabCount]
JNIEXPORT jintArray JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSnapshotInts(JNIEnv* env,
                                                                    jobject,
                                                                    jlong handle) {
    GUARD_BEGIN
    const editor::EditorSnapshot& snapshot = modelFrom(handle)->snapshot();

    jint values[6];
    values[0] = static_cast<jint>(snapshot.selectedIndex);
    values[1] = static_cast<jint>(snapshot.selection.start);
    values[2] = static_cast<jint>(snapshot.selection.end);
    values[3] = snapshot.canUndo ? 1 : 0;
    values[4] = snapshot.canRedo ? 1 : 0;
    values[5] = static_cast<jint>(snapshot.tabs.size());

    jintArray result = env->NewIntArray(6);
    if (result == nullptr) return nullptr;
    env->SetIntArrayRegion(result, 0, 6, values);
    return result;
    GUARD_END(nullptr)
}

// Four entries per tab: id (decimal), fileName, filePath (null when unset),
// dirty ("1" / "0"). One call keeps the per-frame JNI traffic to a handful of
// crossings regardless of how many tabs are open.
JNIEXPORT jobjectArray JNICALL
Java_com_example_myapplication_core_NativeEditor_nativeSnapshotTabs(JNIEnv* env,
                                                                    jobject,
                                                                    jlong handle) {
    GUARD_BEGIN
    const editor::EditorSnapshot& snapshot = modelFrom(handle)->snapshot();
    const jsize count = static_cast<jsize>(snapshot.tabs.size());

    jclass stringClass = env->FindClass("java/lang/String");
    if (stringClass == nullptr) return nullptr;

    jobjectArray result = env->NewObjectArray(count * 4, stringClass, nullptr);
    if (result == nullptr) return nullptr;

    for (jsize i = 0; i < count; ++i) {
        const editor::TabInfo& tab = snapshot.tabs[static_cast<size_t>(i)];

        const std::string id = std::to_string(tab.id);
        jstring jId = env->NewStringUTF(id.c_str());
        env->SetObjectArrayElement(result, i * 4 + 0, jId);
        env->DeleteLocalRef(jId);

        jstring jName = toJava(env, tab.fileName);
        env->SetObjectArrayElement(result, i * 4 + 1, jName);
        env->DeleteLocalRef(jName);

        if (tab.hasPath) {
            jstring jPath = toJava(env, tab.filePath);
            env->SetObjectArrayElement(result, i * 4 + 2, jPath);
            env->DeleteLocalRef(jPath);
        } else {
            env->SetObjectArrayElement(result, i * 4 + 2, nullptr);
        }

        jstring jDirty = env->NewStringUTF(tab.dirty ? "1" : "0");
        env->SetObjectArrayElement(result, i * 4 + 3, jDirty);
        env->DeleteLocalRef(jDirty);
    }
    return result;
    GUARD_END(nullptr)
}

}  // extern "C"
